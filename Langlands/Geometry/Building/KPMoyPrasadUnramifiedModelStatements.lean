import Langlands.Geometry.Building.KPMinimalCongruentMoyPrasadGroups
import Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCell
import Langlands.BruhatTits.IntegralModels.ModelMorphism
import Langlands.GroupScheme.IntegralModel.CongruenceTower
import Langlands.GroupScheme.Reductive.UnipotentRadical

/-! # The models `𝒢_{x,r}` of KP §8.5 over the maximal unramified integers

Let `K` be the maximal unramified extension `inertiaFixedField F` of a nonarchimedean local
field `F`, with integers `𝒪 = fixedFieldIntegers F`, and let `B` be building data of a group
`H` over `K` whose maximal split torus has a torus as centralizer. For a point `x` of the
apartment and a depth `r ≥ 0`, `B.minimalCongruentMoyPrasad hT x r` is the group `G(K)_{x,r}`
of KP Definition 7.3.3 at the constant concave function `r`, with the minimal congruent
filtration on the torus. This module states, at constant depth, the results of KP §8.5 on the
smooth model `𝒢_{x,r}` of `H` with `𝒢_{x,r}(𝒪) = G(K)_{x,r}`: Theorem 8.5.2,
Proposition 8.5.16, Corollary 8.5.12(2), Corollary 8.5.13 in a corrected form, and
Proposition 8.5.18.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

namespace MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : BuildingData F H) (hT : IsTorus B.centralizer.Z)

/-- `G(K)_{x,r+} = ⋃_{s > r} G(K)_{x,s}` (convention of KP §1.6) for the minimal congruent
Moy–Prasad groups over `K`. The family is decreasing as soon as the torus filtration is
(`moyPrasadWith_antitone`), and then the supremum is the union. -/
def minimalCongruentMoyPrasadPlus (x : B.Apartment) (r : ℝ≥0) : Subgroup (rationalPoints H) :=
  ⨆ (s : ℝ≥0) (_ : r < s), B.minimalCongruentMoyPrasad hT x s

theorem minimalCongruentMoyPrasad_le_minimalCongruentMoyPrasadPlus (x : B.Apartment)
    {r s : ℝ≥0} (h : r < s) :
    B.minimalCongruentMoyPrasad hT x s ≤ B.minimalCongruentMoyPrasadPlus hT x r :=
  le_iSup₂_of_le s h le_rfl

end MaximalUnramified.BuildingData

/-- **KP Theorem 8.5.2 at the constant concave function `f = r`, over the integers of the
maximal unramified extension.** Let `H` be a group over `K = inertiaFixedField F` with building
data `B` whose maximal split torus `S` has a torus `T = Z_H(S)` as centralizer, `x` a point of
the apartment and `r ≥ 0`. Then `G(K)_{x,r}` (minimal congruent torus filtration) is the group
of integral points of a smooth affine model `𝒢_{x,r}` of `H` over `𝒪 = fixedFieldIntegers F`
with geometrically connected fibres. Moreover there are, for `none` (the torus) and for every
relative root `a` (`some a`):

* a representative `incl none` of the centralizer of `S` (that is, of `T`) with a smooth model
  with geometrically connected fibres whose integral points have the image `T(K)_r` in `H(K)`;
* a representative `incl (some a)` of the root subgroup `U_a` with a smooth model with
  geometrically connected fibres whose integral points have the image
  `U_{a,x,r} · U_{2a,x,r}` (the block of KP Definition 7.3.3(1));
* a homomorphism of models from each of these into `𝒢_{x,r}` extending `incl`, which is a
  closed immersion.

For every generic cocharacter `ν` there is a smooth closed subgroup scheme `j : V → 𝒢_{x,r}`
whose generic and special fibres are unipotent such that, for every enumeration `a` of the
indivisible roots positive on `ν`, the multiplication morphism `∏_k 𝒰_{a k} → 𝒢_{x,r}` is an
isomorphism onto `V` followed by `j`; so every ordering of the factors gives the same
subgroup scheme. Applied to `-ν` this is the corresponding assertion for the negative roots.
Finally, for every generic cocharacter `ν` and all enumerations `aneg`, `apos` of the
indivisible roots negative, respectively positive, on `ν`, the multiplication morphism
`∏_{aneg} 𝒰_a × 𝒯_r × ∏_{apos} 𝒰_a → 𝒢_{x,r}` is an open immersion. -/
def UnramifiedMoyPrasadModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))) [IsAffineHom H.X.hom]
    (B : MaximalUnramified.BuildingData F H) (hT : IsTorus B.centralizer.Z)
    (x : B.Apartment) (r : ℝ≥0),
    ∃ M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H,
      M.IsSmooth ∧ M.HasGeometricallyConnectedFibres ∧
      M.integralPoints = B.minimalCongruentMoyPrasad hT x r ∧
      ∃ (A : Option (relativeRoots B.i) →
          GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
        (incl : ∀ o, A o ⟶ H)
        (N : ∀ o, IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) (A o))
        (φ : ∀ o, (N o).Hom M (incl o)),
        (torusCentralizer B.i).IsRepresentedBy (incl none) ∧
        (N none).integralPoints.map (rationalPoints.map (incl none)) =
          (B.minimalCongruentTorusFiltration hT r).map
            (rationalPoints.map B.centralizer.j) ∧
        (∀ a : relativeRoots B.i,
          (RelativeRoot.subgroup B.i a).IsRepresentedBy (incl (some a)) ∧
          (((N (some a)).integralPoints.map (rationalPoints.map (incl (some a))) :
              Subgroup (rationalPoints H)) : Set (rationalPoints H)) =
            B.apartment.filtrationBlock x (fun _ => (r : ℝ)) a) ∧
        (∀ o, (N o).IsSmooth ∧ (N o).HasGeometricallyConnectedFibres ∧
          IsClosedImmersion (φ o).hom.hom.hom.left) ∧
        (∀ ν : cocharacterLattice B.S, IsGenericCocharacter B.i ν →
          ∃ (V : GroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F))))
            (j : V ⟶ M.group),
            IsClosedSubgroup j ∧ Smooth V.X.hom ∧
            IsUnipotent ((baseChange (Spec.algebraMap (fixedFieldIntegers F)
              (inertiaFixedField F))).obj V) ∧
            IsUnipotent ((baseChange (IntegralModel.residueBaseMap
              (fixedFieldIntegers F))).obj V) ∧
            ∀ (n : ℕ) (a : Fin n → relativeRoots B.i), Function.Injective a →
              Set.range (fun k => (a k : characterLattice B.S)) =
                RelativeRoot.indivisiblePositiveRoots B.i ν →
              ∃ e : (∏ᶜ fun k => (N (some (a k))).group).X ≅ V.X,
                e.hom ≫ j.hom.hom =
                  RelativeRoot.orderedMultiplication (fun k => (φ (some (a k))).hom)) ∧
        ∀ ν : cocharacterLattice B.S, IsGenericCocharacter B.i ν →
          ∀ (nneg npos : ℕ) (aneg : Fin nneg → relativeRoots B.i)
            (apos : Fin npos → relativeRoots B.i),
            Function.Injective aneg →
            Set.range (fun j => (aneg j : characterLattice B.S)) =
              RelativeRoot.indivisiblePositiveRoots B.i (-ν) →
            Function.Injective apos →
            Set.range (fun j => (apos j : characterLattice B.S)) =
              RelativeRoot.indivisiblePositiveRoots B.i ν →
            IsOpenImmersion (RelativeRoot.orderedMultiplication
              (H := fun j =>
                (N (BruhatTits.IntegralModels.TorusRootModelFamilyData.orderedIntegralIndex
                  (C := B) aneg apos j)).group)
              (fun j =>
                (φ (BruhatTits.IntegralModels.TorusRootModelFamilyData.orderedIntegralIndex
                  (C := B) aneg apos j)).hom)).left

/-- **KP Proposition 8.5.16 at constant depth, over the maximal unramified integers.** For
every smooth model `M` of `H` over `𝒪 = fixedFieldIntegers F` with `M(𝒪) = G(K)_{x,r}` and
every integer `n ≥ 1`, the `n`-th congruence subgroup `ker(M(𝒪) → M(𝒪/𝔪ⁿ))` is
`G(K)_{x,r+n}`. -/
def UnramifiedMoyPrasadCongruenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))) [IsAffineHom H.X.hom]
    (B : MaximalUnramified.BuildingData F H) (hT : IsTorus B.centralizer.Z)
    (x : B.Apartment) (r : ℝ≥0)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H),
    M.IsSmooth → M.integralPoints = B.minimalCongruentMoyPrasad hT x r →
      ∀ n : ℕ+, M.congruenceSubgroupAt n =
        B.minimalCongruentMoyPrasad hT x (r + ((n : ℕ) : ℝ≥0))

/-- **KP Corollary 8.5.12(2) at constant positive depth.** For `r > 0` the special fibre of
every smooth model `M` of `H` over `𝒪 = fixedFieldIntegers F` with `M(𝒪) = G(K)_{x,r}` is
unipotent. -/
def UnramifiedMoyPrasadUnipotentFibreStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))) [IsAffineHom H.X.hom]
    (B : MaximalUnramified.BuildingData F H) (hT : IsTorus B.centralizer.Z)
    (x : B.Apartment) (r : ℝ≥0)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H),
    0 < r → M.IsSmooth → M.integralPoints = B.minimalCongruentMoyPrasad hT x r →
      IsUnipotent M.specialFibre

/-- **KP Corollary 8.5.13 at the constant concave function `r`, in corrected form.** Let `M`
be a smooth model of `H` over `𝒪 = fixedFieldIntegers F` with `M(𝒪) = G(K)_{x,r}` and let
`i` represent the unipotent radical of its special fibre. The subgroup of `G(K)_{x,r}` of
points whose reduction lies in the image of `i` is `G(K)_{x,0+}` if `r = 0`, and is all of
`G(K)_{x,r}` if `r > 0`. This is KP's `G(K)_{x,f+}` for the function `f+` of Definition 8.5.8:
for the constant function `r > 0` no root `a ∈ Φ̂` has `f(a) + f(-a) = 0`, so `f+ = f`. At
depth zero the preimage is the strict-depth union `⋃_{s>0} G(K)_{x,s}`. At positive depth the
preimage is the whole depth-`r` group, and the strict-depth union `⋃_{s>r} G(K)_{x,s}` can be
a proper subgroup of it: for the split torus `G_m` the two agree at `r = 1/2` and differ at
`r = 1`. -/
def UnramifiedMoyPrasadRadicalPreimageStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))) [IsAffineHom H.X.hom]
    (B : MaximalUnramified.BuildingData F H) (hT : IsTorus B.centralizer.Z)
    (x : B.Apartment) (r : ℝ≥0)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H),
    M.IsSmooth → M.integralPoints = B.minimalCongruentMoyPrasad hT x r →
      ∀ (U : GroupScheme (Spec (CommRingCat.of
          (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
        (i : U ⟶ M.specialFibre), IsUnipotentRadical i →
        (r = 0 → ((rationalPoints.map i).range.comap M.reduction).map M.integralPointMap =
          B.minimalCongruentMoyPrasadPlus hT x 0) ∧
        (0 < r → ((rationalPoints.map i).range.comap M.reduction).map M.integralPointMap =
          B.minimalCongruentMoyPrasad hT x r)

/-- **KP Proposition 8.5.18 at constant depths `r ≤ s`.** For smooth models `M` and `M'` of
`H` over `𝒪 = fixedFieldIntegers F` with `M(𝒪) = G(K)_{x,r}` and `M'(𝒪) = G(K)_{x,s}`, every
homomorphism of models `M' → M` extending the identity of `H` (KP 8.5.17) induces on special
fibres a homomorphism whose scheme-theoretic kernel is smooth, connected and unipotent. -/
def UnramifiedMoyPrasadKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))) [IsAffineHom H.X.hom]
    (B : MaximalUnramified.BuildingData F H) (hT : IsTorus B.centralizer.Z)
    (x : B.Apartment) (r s : ℝ≥0), r ≤ s →
    ∀ (M M' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H),
      M.IsSmooth → M'.IsSmooth →
      M.integralPoints = B.minimalCongruentMoyPrasad hT x r →
      M'.integralPoints = B.minimalCongruentMoyPrasad hT x s →
      ∀ ψ : M'.Hom M (𝟙 _),
        Smooth (kernel ψ.specialFibreMap).X.hom ∧
          ConnectedSpace (kernel ψ.specialFibreMap).X.left ∧
            IsUnipotent (kernel ψ.specialFibreMap)

end Langlands.Geometry.Building
