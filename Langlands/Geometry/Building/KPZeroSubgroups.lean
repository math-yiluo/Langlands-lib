import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.SimplyConnected.DerivedCover
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.Galois.Local.SeparableInertiaDefinitions

/-!
# The subgroups `T(K)^0`, `G(k)^♮` and `G(k)^0` of Kaletha–Prasad

Let `F` be a nonarchimedean local field, `K` the maximal unramified extension of `F` in the
fixed separable closure `F^sep`, and `G` a connected reductive `F`-group. This module defines,
on the actual rational-point groups:

* the maximal bounded subgroup `T(L)^b = {t | ω(χ(t)) = 0 for all χ}` of a split torus
  (KP Proposition 2.5.8), as `characterValuationKernel`;
* the Iwahori subgroup `T(K)^0`, the image of `T(L)^b` under the norm `T(L) → T(K)` for a
  finite Galois extension `L/K` splitting `T` (KP Definition 2.5.13), as `torusNormIwahori`;
* `G(k)^♮`, the image of `G_sc(k) → G(k)` (KP Definition 2.6.20), as `simplyConnectedImage`;
* maximally split maximal tori (KP Definition 2.6.2);
* `H(K)^0 = H(K)^♮ · T(K)^0` (KP Definition 2.6.23(1)) and `M(F)^0 = M(K)^0 ∩ M(F)`
  (KP Definition 2.6.23(2)), from `UnramifiedZeroDatum`;
* `G(F)^0 = G(F)^♮ · M_0(F)^0` for the minimal Levi subgroup `M_0 = Z_G(S)`
  (KP Definition 2.6.23(3)), from `ZeroSubgroupDatum`.

KP's products of subgroups are formed here as joins `⊔` (generated subgroups). The choices
(of `L`, `T`, the simply connected cover and `S`) are data. The independence of these choices
(KP Lemmas 2.5.12 and 2.6.24), the normality of `G(k)^♮`, and the equality of the joins with
the product sets are not proved here. Nothing asserts that the data exist.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-! ### Constructions over an arbitrary field -/

section Field

variable {k : Type u} [Field k] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- `{g ∈ G(k) | v(χ(g)) = 1 for every χ ∈ X^*_k(G)}`, the common kernel of the valuations of
the rational characters. For a `k`-torus `T` and `v` the valuation of `k`, the rational
characters are `X^*(T)^Θ`, so this is the maximal bounded subgroup
`T(k)^b = {t | ω(χ(t)) = 0 for all χ ∈ X^*(T)^Θ}` of KP Proposition 2.5.8 (second
description), written multiplicatively. For `T` split over `k` it is also the third. -/
def characterValuationKernel (v : Valuation k Γ₀) (G : GroupScheme (Spec (CommRingCat.of k))) :
    Subgroup (rationalPoints G) :=
  ⨅ χ : rationalCharacters G, ((Units.map v.toMonoidHom).comp (rationalCharacterEval χ)).ker

theorem mem_characterValuationKernel {v : Valuation k Γ₀}
    {G : GroupScheme (Spec (CommRingCat.of k))} {g : rationalPoints G} :
    g ∈ characterValuationKernel v G ↔
      ∀ χ : rationalCharacters G, v (rationalCharacterEval χ g : k) = 1 := by
  simp only [characterValuationKernel, Subgroup.mem_iInf, MonoidHom.mem_ker,
    MonoidHom.comp_apply, Units.ext_iff, Units.coe_map, Units.val_one]
  rfl

instance characterValuationKernel_normal (v : Valuation k Γ₀)
    (G : GroupScheme (Spec (CommRingCat.of k))) : (characterValuationKernel v G).Normal :=
  Subgroup.normal_iInf_normal fun _ => MonoidHom.normal_ker _

variable {D C G : GroupScheme (Spec (CommRingCat.of k))}

/-- `G(k)^♮`, the image of `C(k) → G(k)` for maps `π : C → D` and `d : D → G`. When
`IsSimplyConnectedDerivedCover d π` holds, `D` is the derived subgroup of `G` and `C = G_sc`
its simply connected cover, so this is the image of `G_sc(k) → G(k)` of KP
Definition 2.6.20. -/
def simplyConnectedImage (d : D ⟶ G) (π : C ⟶ D) : Subgroup (rationalPoints G) :=
  (rationalPoints.map (π ≫ d)).range

theorem mem_simplyConnectedImage {d : D ⟶ G} {π : C ⟶ D} {g : rationalPoints G} :
    g ∈ simplyConnectedImage d π ↔ ∃ c : rationalPoints C, rationalPoints.map (π ≫ d) c = g :=
  MonoidHom.mem_range

/-- A maximal torus `i : T → G` is maximally split when its maximal split subtorus is a
maximal split torus of `G` (KP Definition 2.6.2). Here: `T` contains a maximal split torus
`a : A → G` of `G`, that is, `a = f ≫ i` for some `f : A → T`. -/
def IsMaximallySplitMaximalTorus {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) : Prop :=
  IsMaximalTorus i ∧
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G)
      (f : A.toGrp ⟶ T.toGrp), IsMaximalSplitTorus a ∧ f ≫ i = a

end Field

/-! ### The norm image of the bounded subgroup -/

section Norm

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The commutative base change used by the norm has the group scheme `T_L` as underlying
group scheme. -/
theorem baseChange_toGrp (T : CommGroupScheme (Spec (CommRingCat.of K))) :
    ((CommGroupScheme.baseChange (GaloisPointComparison.baseMap K L)).obj T).toGrp =
      GaloisPointComparison.baseChanged K L T.toGrp :=
  rfl

/-- The image of `characterValuationKernel v T_L` under the norm `T(L) → T(K)` of the finite
Galois extension `L/K`. When `L` splits `T` and `v` is the valuation of `L` extending that of
`K`, this is the Iwahori subgroup `T(K)^0` of KP Definition 2.5.13. -/
def torusNormIwahori (v : Valuation L Γ₀) (T : CommGroupScheme (Spec (CommRingCat.of K)))
    [IsAffine T.X.left] : Subgroup (rationalPoints T.toGrp) :=
  (characterValuationKernel v
    ((CommGroupScheme.baseChange (GaloisPointComparison.baseMap K L)).obj T).toGrp).map
      (GaloisPointComparison.rationalNorm K L T)

theorem mem_torusNormIwahori {v : Valuation L Γ₀}
    {T : CommGroupScheme (Spec (CommRingCat.of K))} [IsAffine T.X.left]
    {t : rationalPoints T.toGrp} :
    t ∈ torusNormIwahori K L v T ↔
      ∃ x ∈ characterValuationKernel v
          ((CommGroupScheme.baseChange (GaloisPointComparison.baseMap K L)).obj T).toGrp,
        GaloisPointComparison.rationalNorm K L T x = t :=
  Subgroup.mem_map

end Norm

/-! ### The local field `F` and its maximal unramified extension `K` -/

section Local

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- KP's `K`: the maximal unramified extension of `F` in the separable closure `F^sep`, the
fixed field of the inertia subgroup of `Gal(F^sep/F)`. -/
abbrev UnramifiedClosure : Type u :=
  LocalGalois.Separable.inertiaFixedField F

/-- The valuation of an intermediate field `L` of `F^sep/K`: the restriction of the unique
(spectral) extension to `F^sep` of the valuation of `F`. -/
def intermediateValuation (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F)) :
    Valuation L ℝ≥0 :=
  (LocalGalois.Separable.sepClosureValuation F).comap (algebraMap L (SeparableClosure F))

theorem intermediateValuation_apply
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F)) (x : L) :
    intermediateValuation F L x =
      LocalGalois.Separable.sepClosureValuation F (x : SeparableClosure F) :=
  rfl

/-- Data for KP Definition 2.6.23(1) for a `K`-group `H`: a maximally split maximal torus
`i : T → H`, a finite Galois extension `L/K` inside `F^sep` splitting `T`, and a simply
connected cover `π : C → D` of the derived subgroup `d : D → H`. Over `K` every connected
reductive group is quasi-split (KP Corollary 2.3.8), which is not a field here. -/
structure UnramifiedZeroDatum (H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))) :
    Type (u + 1) where
  /-- The maximal torus `T`. -/
  T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))
  [isAffine : IsAffine T.X.left]
  /-- The inclusion `T → H`. -/
  i : T.toGrp ⟶ H
  isMaximallySplitMaximalTorus : IsMaximallySplitMaximalTorus i
  /-- The finite Galois splitting field `L ⊆ F^sep` of `T`. -/
  L : IntermediateField (UnramifiedClosure F) (SeparableClosure F)
  [finiteDimensional : FiniteDimensional (UnramifiedClosure F) L]
  [isGalois : IsGalois (UnramifiedClosure F) L]
  isSplitTorus : IsSplitTorus (GaloisPointComparison.baseChanged (UnramifiedClosure F) L T.toGrp)
  /-- The derived subgroup `D` of `H`. -/
  D : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))
  /-- The simply connected cover `C = D_sc`. -/
  C : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))
  /-- The inclusion `D → H`. -/
  d : D ⟶ H
  /-- The covering map `C → D`. -/
  π : C ⟶ D
  isSimplyConnectedDerivedCover : IsSimplyConnectedDerivedCover d π

namespace UnramifiedZeroDatum

attribute [instance] isAffine finiteDimensional isGalois

variable {F} {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  (E : UnramifiedZeroDatum F H)

/-- The Iwahori subgroup `T(K)^0` of KP Definition 2.5.13: the image of `T(L)^b` under the norm
`T(L) → T(K)`. -/
def torusIwahori : Subgroup (rationalPoints E.T.toGrp) :=
  torusNormIwahori (UnramifiedClosure F) E.L (intermediateValuation F E.L) E.T

/-- `H(K)^♮`, the image of `H_sc(K) → H(K)` (KP Definition 2.6.20). -/
def simplyConnectedImage : Subgroup (rationalPoints H) :=
  Building.simplyConnectedImage E.d E.π

/-- `H(K)^0 = H(K)^♮ · T(K)^0` (KP Definition 2.6.23(1)). -/
def zeroPoints : Subgroup (rationalPoints H) :=
  E.simplyConnectedImage ⊔ E.torusIwahori.map (rationalPoints.map E.i)

theorem simplyConnectedImage_le_zeroPoints : E.simplyConnectedImage ≤ E.zeroPoints :=
  le_sup_left

theorem map_torusIwahori_le_zeroPoints :
    E.torusIwahori.map (rationalPoints.map E.i) ≤ E.zeroPoints :=
  le_sup_right

end UnramifiedZeroDatum

variable {F}

/-- `M(F)^0 = M(K)^0 ∩ M(F)` for an `F`-group `M` that is anisotropic modulo its center,
with `M(K)^0` given by KP Definition 2.6.23(1) for `M_K` (KP Definition 2.6.23(2)). Here
`M(F)` is a subgroup of `M(K)` through the published extension of scalars. -/
def anisotropicZeroPoints {M : GroupScheme (Spec (CommRingCat.of F))}
    (E : UnramifiedZeroDatum F (GaloisPointComparison.baseChanged F (UnramifiedClosure F) M)) :
    Subgroup (rationalPoints M) :=
  E.zeroPoints.comap (GaloisPointComparison.rationalExtend F (UnramifiedClosure F) M)

theorem mem_anisotropicZeroPoints {M : GroupScheme (Spec (CommRingCat.of F))}
    {E : UnramifiedZeroDatum F (GaloisPointComparison.baseChanged F (UnramifiedClosure F) M)}
    {m : rationalPoints M} :
    m ∈ anisotropicZeroPoints E ↔
      GaloisPointComparison.rationalExtend F (UnramifiedClosure F) M m ∈ E.zeroPoints :=
  Subgroup.mem_comap

/-! ### `G(F)^0` -/

variable {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}

/-- Data for KP Definition 2.6.23(3) of `G(F)^0`, relative to a maximal split torus
`i : S → G` and the minimal Levi subgroup `j : Z → G`, `Z = Z_G(S)`: data of KP
Definition 2.6.23(1) for `Z_K`, and a simply connected cover `π : C → D` of the derived
subgroup `d : D → G`. -/
structure ZeroSubgroupDatum (i : S.toGrp ⟶ G) (j : Z ⟶ G) : Type (u + 1) where
  isMaximalSplitTorus : IsMaximalSplitTorus i
  /-- `j` represents the centralizer of `S`, so `Z = Z_G(S)` is a minimal Levi subgroup. -/
  isRepresentedBy : (torusCentralizer i).IsRepresentedBy j
  /-- Data of KP Definition 2.6.23(1) for `Z_K`. -/
  centralizerDatum :
    UnramifiedZeroDatum F (GaloisPointComparison.baseChanged F (UnramifiedClosure F) Z)
  /-- The derived subgroup `D` of `G`. -/
  D : GroupScheme (Spec (CommRingCat.of F))
  /-- The simply connected cover `C = G_sc`. -/
  C : GroupScheme (Spec (CommRingCat.of F))
  /-- The inclusion `D → G`. -/
  d : D ⟶ G
  /-- The covering map `C → D`. -/
  π : C ⟶ D
  isSimplyConnectedDerivedCover : IsSimplyConnectedDerivedCover d π

namespace ZeroSubgroupDatum

variable {i : S.toGrp ⟶ G} {j : Z ⟶ G} (E : ZeroSubgroupDatum i j)

/-- `Z(F)^0 = Z(K)^0 ∩ Z(F)` for the minimal Levi subgroup `Z = Z_G(S)`, which is anisotropic
modulo its center (KP Definition 2.6.23(2)). -/
def centralizerZero : Subgroup (rationalPoints Z) :=
  anisotropicZeroPoints E.centralizerDatum

/-- `G(F)^♮`, the image of `G_sc(F) → G(F)` (KP Definition 2.6.20). -/
def simplyConnectedImage : Subgroup (rationalPoints G) :=
  Building.simplyConnectedImage E.d E.π

/-- `G(F)^0 = G(F)^♮ · M_0(F)^0` with `M_0 = Z_G(S)` (KP Definition 2.6.23(3)). -/
def zeroSubgroup : Subgroup (rationalPoints G) :=
  E.simplyConnectedImage ⊔ E.centralizerZero.map (rationalPoints.map j)

theorem simplyConnectedImage_le_zeroSubgroup : E.simplyConnectedImage ≤ E.zeroSubgroup :=
  le_sup_left

theorem map_centralizerZero_le_zeroSubgroup :
    E.centralizerZero.map (rationalPoints.map j) ≤ E.zeroSubgroup :=
  le_sup_right

end ZeroSubgroupDatum

end Local

end Langlands.Geometry.Building
