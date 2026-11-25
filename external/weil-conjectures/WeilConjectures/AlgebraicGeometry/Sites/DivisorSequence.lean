/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.AlgebraicGeometry.Sites.DivisorMap
public import WeilConjectures.AlgebraicGeometry.Sites.DivisorLocal
public import WeilConjectures.AlgebraicGeometry.Sites.GmGenericPoint
public import WeilConjectures.AlgebraicGeometry.Sites.StalkwiseCokernel
public import WeilConjectures.Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90Etale
public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.EdgeMap

/-!
# The divisor sequence and the generic-point injection for the Brauer group

For an integral regular noetherian scheme `X` with generic point `i : Spec k(X) ⟶ X` there is
a short exact sequence of étale sheaves

```
  0 ──▶ 𝔾ₘ ──unit──▶ i_* i^* 𝔾ₘ ──div──▶ ∐_{x ∈ X⁽¹⁾} i_{x*} ℤ ──▶ 0
```

the third map sending a rational function to its divisor. The points of `X⁽¹⁾` are the points
of coheight one, and `i_{x*} ℤ` is the pushforward of the constant sheaf `ℤ` along
`Spec κ(x) ⟶ X`. Taking the long exact cohomology sequence and using
`H¹(X, i_{x*} ℤ) = 0`, together with the vanishing of `R¹i_* 𝔾ₘ` for the Leray spectral
sequence of `i`, gives Grothendieck's residue injection

```
   Spec k(X) ──── i ────▶ X            H²(X_ét, 𝔾ₘ)
                                            │ cohomologyMap i 𝔾ₘ 2  (injective)
                                            ▼
                                       H²(Spec k(X)_ét, i^* 𝔾ₘ)
```

whose target is `H²(Spec k(X)_ét, 𝔾ₘ) = Br(k(X))` by
`AlgebraicGeometry.Scheme.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField`.

## Main definitions

- `AlgebraicGeometry.Scheme.genericGm`: the sheaf `i_* i^* 𝔾ₘ`.
- `AlgebraicGeometry.Scheme.toGenericGm`: the unit `𝔾ₘ ⟶ i_* i^* 𝔾ₘ`, the first map of the
  divisor sequence.
- `AlgebraicGeometry.Scheme.pointConstantInt`: the sheaf `i_{x*} ℤ` of a point `x` of `X`.
- `AlgebraicGeometry.Scheme.divisorSequenceMap`: the divisor map
  `i_* i^* 𝔾ₘ ⟶ ⨁_{x ∈ X⁽¹⁾} i_{x*} ℤ`, `f ↦ ∑_x ord_x(f) [x]`, the second map of the divisor
  sequence.

## Main statements

- `AlgebraicGeometry.Scheme.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField`: the
  pullback of `𝔾ₘ` along the generic point is `𝔾ₘ`.
- `AlgebraicGeometry.Scheme.mono_toGenericGm`: the unit `𝔾ₘ ⟶ i_* i^* 𝔾ₘ` is a monomorphism.
- `AlgebraicGeometry.Scheme.exists_cokernel_toGenericGm_iso_hom_comp_eq`: its cokernel is
  `⨁_{x ∈ X⁽¹⁾} i_{x*} ℤ`, compatibly with the divisor map, from three local statements on
  étale neighbourhoods.
- `AlgebraicGeometry.Scheme.shortExact_divisorSequence`: the divisor sequence, with the unit
  and the divisor map, is short exact, from the two previous statements.
- `AlgebraicGeometry.Scheme.subsingleton_H_one_pointConstantInt`: `H¹(X, i_{x*} ℤ) = 0`.
- `AlgebraicGeometry.Scheme.epi_lowerStar_map_cokernelπ_upperStar_gmSheaf`: `R¹i_* 𝔾ₘ = 0`
  along the generic point.
- `AlgebraicGeometry.Scheme.injective_cohomologyMap_gmSheaf_two`: the map
  `Br(X) = H²(X, 𝔾ₘ) → H²(Spec k(X), 𝔾ₘ) = Br(k(X))` along the generic point is injective.

## TODO

The third term is a colimit cocone taken as an argument rather than the coproduct
`∐ fun x ↦ X.pointConstantInt x`. The sheaf category is Grothendieck abelian, so the
coproduct does exist, but synthesising `Limits.HasCoproduct` for a family indexed by a type
in the universe of the points of `X` does not terminate in a usable time here; it should be
replaced by `∐ …` once that is fixed.

## Implementation details

The comparison `i^* 𝔾ₘ ≅ 𝔾ₘ` along the (non-étale) generic point is checked on stalks via
`AlgebraicGeometry.Etale.stalkComparison`. Exactness of the divisor sequence is checked on
geometric stalks, where both `i_* 𝔾ₘ` and `⨁_x i_{x*} ℤ` map to the sheaf `V ↦ (V → ℤ)` of
functions on points. The vanishing `R¹i_* 𝔾ₘ = 0` is proved on sections, by Hilbert 90 over
the generic fibre of affine étale `X`-schemes, rather than via `Pic` of strict henselisations.
-/

@[expose] public section

universe u

open CategoryTheory Limits Order

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The étale sheaf `i_* i^* 𝔾ₘ` on `X`, the pushforward along the generic point
`i : Spec k(X) ⟶ X` of the pullback of `𝔾ₘ`. -/
noncomputable def genericGm : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj
    ((Etale.upperStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj X.gmSheaf)

/-- The unit `𝔾ₘ ⟶ i_* i^* 𝔾ₘ` of the adjunction
`AlgebraicGeometry.Etale.upperStarLowerStarAdjunction` at the generic point: the first map of
the divisor sequence. -/
noncomputable def toGenericGm : X.gmSheaf ⟶ X.genericGm :=
  (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} X.fromSpecFunctionField).unit.app
    X.gmSheaf

/-- The comparison map `i^* 𝔾ₘ ⟶ 𝔾ₘ` along the generic point `i : Spec k(X) ⟶ X` is an
isomorphism. -/
theorem isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField :
    IsIso (upperStarGmSheafToGmSheaf X.fromSpecFunctionField) := by
  refine isIso_of_isIso_sheafFiber_map _ fun t ↦ ?_
  rw [uliftPointSmallEtale, NatIso.isIso_map_iff
    ((pointSmallEtale _).uliftSheafFiberIso AddCommGrpCat.{u + 1}) _]
  have h := Etale.upperStarCompSheafFiberIso_inv_app_comp_sheafFiber_map
    X.fromSpecFunctionField ((Spec X.functionField).algClosurePoint t)
    (gmSheafToLowerStarGmSheaf X.fromSpecFunctionField)
  have : IsIso (Etale.stalkComparison X.fromSpecFunctionField
      ((Spec X.functionField).algClosurePoint t)
      (gmSheafToLowerStarGmSheaf X.fromSpecFunctionField)) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨Etale.injective_stalkComparison_gmSheafToLowerStarGmSheaf X _,
        Etale.surjective_stalkComparison_gmSheafToLowerStarGmSheaf X _⟩
  rw [← h] at this
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance this

/-- The isomorphism of `i_* i^* 𝔾ₘ` with the pushforward of the sheaf `𝔾ₘ` of `Spec k(X)`. -/
noncomputable def genericGmIso : X.genericGm ≅
    (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj
      (Spec X.functionField).gmSheaf :=
  haveI := X.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField
  (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).mapIso
    (asIso (upperStarGmSheafToGmSheaf X.fromSpecFunctionField))

/-- The étale sheaf `i_{x*} ℤ` on `X`: the pushforward of the constant sheaf `ℤ` along the
canonical morphism `Spec κ(x) ⟶ X` of a point `x` of `X`. -/
noncomputable def pointConstantInt (x : X) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} (X.fromSpecResidueField x)).obj
    ((constantSheaf _ AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- The first map of the divisor sequence is injective: `𝔾ₘ ⟶ i_* 𝔾ₘ` along the generic point
`i : Spec k(X) ⟶ X` is a monomorphism. -/
theorem mono_gmSheafToLowerStarGmSheaf_fromSpecFunctionField :
    Mono (gmSheafToLowerStarGmSheaf X.fromSpecFunctionField) := by
  refine Sheaf.Hom.mono_of_presheaf_mono _ _ _ (h := ?_)
  suffices ∀ V, Mono ((gmSheafToLowerStarGmSheaf X.fromSpecFunctionField).hom.app V) from
    NatTrans.mono_of_mono_app _
  intro V
  rw [AddCommGrpCat.mono_iff_injective]
  intro a b h
  have hinj := X.injective_Γ_map_pullback_fst_fromSpecFunctionField V.unop.hom
  exact ULift.ext (Units.ext (hinj (congrArg (fun x ↦ (Additive.toMul x.down).val) h)))

/-- **The unit `𝔾ₘ ⟶ i_* i^* 𝔾ₘ` is a monomorphism**, the left exactness of the divisor
sequence. -/
theorem mono_toGenericGm : Mono X.toGenericGm := by
  have h := X.mono_gmSheafToLowerStarGmSheaf_fromSpecFunctionField
  have e : X.toGenericGm ≫ (Etale.lowerStar _ _).map
      (upperStarGmSheafToGmSheaf X.fromSpecFunctionField) =
      gmSheafToLowerStarGmSheaf X.fromSpecFunctionField := by
    simp [toGenericGm, upperStarGmSheafToGmSheaf, Adjunction.homEquiv_counit]
  rw [← e] at h
  exact mono_of_mono _ ((Etale.lowerStar _ _).map (upperStarGmSheafToGmSheaf _))

/-- The map `i_{x*} ℤ ⟶ (V ↦ (V → ℤ))` from the sheaf of a point `x` to the sheaf of functions on
points, viewing a section of `ℤ` over `V ×_X Spec κ(x)` as a function on the points of `V`
over `x` and extending it by zero to all of `V`. -/
noncomputable def pointConstantIntToPointFunctionSheaf (x : X) :
    X.pointConstantInt x ⟶ X.pointFunctionSheaf (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} (X.fromSpecResidueField x)).map
      ((Spec (X.residueField x)).constantSheafToPointFunctionSheaf _) ≫
    lowerStarPointFunctionSheafToPointFunctionSheaf _ (X.fromSpecResidueField x)

instance isIso_constantSheafToPointFunctionSheaf_residueField (x : X)
    (M : AddCommGrpCat.{u + 1}) :
    IsIso ((Spec (X.residueField x)).constantSheafToPointFunctionSheaf M) :=
  isIso_constantSheafToPointFunctionSheaf M discreteTopology_of_etale_of_unique

/-- The map `(V ↦ (V → ℤ)) ⟶ i_{x*} ℤ` restricting a function on the points of `V` to the
points of `V` over `x`. It is a retraction of
`AlgebraicGeometry.Scheme.pointConstantIntToPointFunctionSheaf`. -/
noncomputable def pointFunctionSheafToPointConstantInt (x : X) :
    X.pointFunctionSheaf (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ X.pointConstantInt x :=
  pointFunctionSheafToLowerStar _ (X.fromSpecResidueField x) ≫
    (Etale.lowerStar AddCommGrpCat.{u + 1} (X.fromSpecResidueField x)).map
      (inv ((Spec (X.residueField x)).constantSheafToPointFunctionSheaf _))

omit [IsIntegral X] in
@[reassoc (attr := simp)]
lemma pointConstantIntToPointFunctionSheaf_comp_self (x : X) :
    X.pointConstantIntToPointFunctionSheaf x ≫ X.pointFunctionSheafToPointConstantInt x = 𝟙 _ := by
  simp [pointConstantIntToPointFunctionSheaf, pointFunctionSheafToPointConstantInt]

omit [IsIntegral X] in
lemma pointConstantIntToPointFunctionSheaf_comp_of_ne {x x' : X} (h : x ≠ x') :
    X.pointConstantIntToPointFunctionSheaf x ≫ X.pointFunctionSheafToPointConstantInt x' = 0 := by
  have hd : Disjoint (Set.range (X.fromSpecResidueField x))
      (Set.range (X.fromSpecResidueField x')) := by
    rw [range_fromSpecResidueField, range_fromSpecResidueField]
    exact Set.disjoint_singleton.2 h
  simp only [pointConstantIntToPointFunctionSheaf, pointFunctionSheafToPointConstantInt,
    Category.assoc]
  rw [reassoc_of% (lowerStarPointFunctionSheafToPointFunctionSheaf_comp_eq_zero _ _ _ hd),
    zero_comp, comp_zero]

omit [IsIntegral X] in
lemma pointFunctionSheafToPointConstantInt_comp (x : X) :
    X.pointFunctionSheafToPointConstantInt x ≫ X.pointConstantIntToPointFunctionSheaf x =
      pointFunctionSheafToLowerStar _ (X.fromSpecResidueField x) ≫
        lowerStarPointFunctionSheafToPointFunctionSheaf _ (X.fromSpecResidueField x) := by
  simp only [pointFunctionSheafToPointConstantInt, pointConstantIntToPointFunctionSheaf,
    Category.assoc]
  rw [← Functor.map_comp_assoc, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

omit [IsIntegral X] in
open Classical in
/-- Restricting a function on the points of `V` to the points over `x` and extending by zero
keeps its values over `x` and kills the others. -/
lemma extendByZero_fromSpecResidueField_fst (M : AddCommGrpCat.{u + 1}) (V : X.Etale) (x : X)
    (D : V.left → M) (y : V.left) :
    extendByZero M (X.fromSpecResidueField x)
        (fun z ↦ D (pullback.fst V.hom (X.fromSpecResidueField x) z)) y =
      if V.hom y = x then D y else 0 := by
  split_ifs with h
  · have hy : y ∈ Set.range (pullback.fst V.hom (X.fromSpecResidueField x)) := by
      refine (Set.ext_iff.1 (Scheme.Pullback.range_fst V.hom (X.fromSpecResidueField x)) y).2 ?_
      change V.hom y ∈ Set.range (X.fromSpecResidueField x)
      rw [range_fromSpecResidueField, h]
      rfl
    obtain ⟨z, rfl⟩ := hy
    exact extendByZero_fst _ z
  · refine extendByZero_of_notMem _ ?_
    rw [range_fromSpecResidueField]
    exact h

/-- The divisor map vanishes on units: the composite `𝔾ₘ ⟶ i_* 𝔾ₘ ⟶ (V ↦ (V → ℤ))` is zero. -/
lemma gmSheafToLowerStarGmSheaf_comp_divisorMap [IsLocallyNoetherian X] [IsRegular X] :
    gmSheafToLowerStarGmSheaf X.fromSpecFunctionField ≫ X.divisorMap = 0 := by
  ext V u
  funext y
  exact ULift.ext (Etale.ord_fst_appTop V.unop y _)

/-- **Local algebraic Hartogs on an étale neighbourhood.** Let `X` be an integral regular
locally noetherian scheme, `V` an étale `X`-scheme and `f` a unit on the generic fibre of `V`
whose order vanishes at every point of `V`. Then near every point `y` of `V` the function `f`
is a unit of `𝒪_V`: there is an open neighbourhood `U` of `y` and `u ∈ Γ(U, 𝒪)ˣ` restricting
to `f` on the generic fibre of `U`. -/
lemma Etale.exists_eq_of_ord_eq_zero [IsLocallyNoetherian X] [IsRegular X] (V : X.Etale)
    (y : V.left) (f : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)ˣ)
    (hf : ∀ y', Etale.ord V y' f = 0) :
    ∃ (U : V.left.Opens) (_ : y ∈ U) (u : Γ(Etale.ofOpens V U |>.left, ⊤)ˣ),
      (pullback.fst (Etale.ofOpens V U).hom X.fromSpecFunctionField).appTop u.val =
        ((MorphismProperty.Over.pullback @Etale ⊤ X.fromSpecFunctionField).map
          (Etale.ofOpensι V U)).left.appTop f.val := by
  obtain ⟨r, hr⟩ := Etale.exists_toLocalGenericRing_eq_of_ord_eq_zero V y f fun w _ ↦ hf w
  exact Etale.exists_eq_of_toLocalGenericRing_eq V y f.val r hr

/-- **Local finiteness of divisors.** Let `X` be an integral regular locally noetherian scheme,
`V` an étale `X`-scheme and `f` a unit on the generic fibre of `V`. Near every point of `V`, the
points at which `f` has nonzero order lie over finitely many points of `X`. -/
lemma Etale.exists_finset_of_ord_ne_zero [IsLocallyNoetherian X] [IsRegular X] (V : X.Etale)
    (y : V.left) (f : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)ˣ) :
    ∃ (U : V.left.Opens) (_ : y ∈ U) (T : Finset X),
      ∀ y' ∈ U, Etale.ord V y' f ≠ 0 → V.hom y' ∈ T := by
  classical
  obtain ⟨U, hyU, hfin⟩ := Etale.exists_opens_finite_ord_ne_zero V y f
  exact ⟨U, hyU, hfin.toFinset.image V.hom, fun y' hy' h ↦
    Finset.mem_image.2 ⟨y', hfin.mem_toFinset.2 ⟨hy', h⟩, rfl⟩⟩

/-- **Weil divisors are locally principal on an étale neighbourhood.** Let `X` be an integral
regular locally noetherian scheme, `x` a point of `X` of codimension one, `V` an étale
`X`-scheme and `c` an integer-valued function on the points of `V` over `x`. Near every point
`y` of `V` there is a unit on the generic fibre whose order is `c` at the points over `x` and `0`
elsewhere. -/
lemma Etale.exists_ord_eq_extendByZero [IsLocallyNoetherian X] [IsRegular X] (V : X.Etale)
    (y : V.left) {x : X} (hx : coheight x = 1)
    (c : ↥(pullback V.hom (X.fromSpecResidueField x)) → ULift.{u + 1} ℤ) :
    ∃ (U : V.left.Opens) (_ : y ∈ U)
      (f : Γ(pullback (Etale.ofOpens V U).hom X.fromSpecFunctionField, ⊤)ˣ),
      ∀ y' : U, ULift.up (Etale.ord (Etale.ofOpens V U) y' f) =
        extendByZero (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (X.fromSpecResidueField x) c
          (U.ι y') := by
  obtain ⟨U, hyU, f, hf⟩ := Etale.exists_ord_eq_of_forall_ne V y hx
    (fun z ↦
      (extendByZero (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (X.fromSpecResidueField x) c z).down)
    fun z hz ↦ by
      rw [extendByZero_of_notMem _ (by rwa [range_fromSpecResidueField])]
      rfl
  exact ⟨U, hyU, f, fun y' ↦ ULift.ext (hf y')⟩

omit [IsIntegral X] in
/-- On geometric stalks, extension by zero `⨁_{i} i_{e(i)*} ℤ ⟶ (V ↦ (V → ℤ))` is injective, for
an injective family `e` of points of `X`. -/
lemma injective_sheafFiber_map_desc_pointConstantIntToPointFunctionSheaf {ι : Type u}
    {e : ι → X} (he : Function.Injective e) (c : Cofan fun i ↦ X.pointConstantInt (e i))
    (hc : IsColimit c) (s : X) :
    Function.Injective ((X.uliftPointSmallEtale s).sheafFiber.map
      (Cofan.IsColimit.desc hc fun i ↦ X.pointConstantIntToPointFunctionSheaf (e i))) := by
  let F := (X.uliftPointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  have hc' : IsColimit (Cofan.mk c.pt c.inj) :=
    hc.ofIsoColimit (Cofan.ext (Iso.refl _) (fun _ ↦ Category.comp_id _))
  have hd := isColimitCofanMkObjOfIsColimit F _ c.inj hc'
  refine AddCommGrpCat.injective_of_isColimit_cofan hd _
    (fun i ↦ F.map (X.pointFunctionSheafToPointConstantInt (e i))) (fun i ↦ ?_)
    (fun i i' h ↦ ?_)
  · change F.map _ ≫ F.map _ ≫ F.map _ = _
    rw [← F.map_comp, ← F.map_comp, Cofan.IsColimit.fac_assoc,
      pointConstantIntToPointFunctionSheaf_comp_self, F.map_id]
  · change F.map _ ≫ F.map _ ≫ F.map _ = _
    rw [← F.map_comp, ← F.map_comp, Cofan.IsColimit.fac_assoc,
      pointConstantIntToPointFunctionSheaf_comp_of_ne _ (fun h' ↦ h (he h')), F.map_zero]

omit [IsIntegral X] in
/-- The image of a geometric point of an étale `X`-scheme lies in every open subscheme
containing its closed point. -/
lemma range_uliftPointSmallEtale_fiber_subset {s : X} {V : X.Etale}
    (v : (X.uliftPointSmallEtale s).fiber.obj V) (U : V.left.Opens)
    (hU : v.down.left (IsLocalRing.closedPoint _) ∈ U) :
    Set.range v.down.left ⊆ (U : Set V.left) := by
  rintro _ ⟨z, rfl⟩
  have : Subsingleton (Spec (.of (AlgebraicClosure (X.residueField s)))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum _))
  rwa [show z = IsLocalRing.closedPoint _ from @Subsingleton.elim _ this z _]

omit [IsIntegral X] in
/-- **Germs in the image of a point sheaf, from a local statement.** Let `d : B ⟶ (V ↦ (V → ℤ))`
be a morphism of étale sheaves and `x` a point of `X`. Suppose that every function obtained by
extending by zero a function on the points of an étale `X`-scheme `V` over `x` is, near every
point of `V`, the image under `d` of a section of `B`. Then on geometric stalks the image of
`i_{x*} ℤ ⟶ (V ↦ (V → ℤ))` is contained in that of `d`. -/
lemma exists_sheafFiber_eq_pointConstantIntToPointFunctionSheaf
    {B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (d : B ⟶ X.pointFunctionSheaf (AddCommGrpCat.of (ULift.{u + 1} ℤ))) (x : X)
    (hd : ∀ (V : X.Etale) (y : V.left)
      (c : ↥(pullback V.hom (X.fromSpecResidueField x)) → ULift.{u + 1} ℤ),
      ∃ (U : V.left.Opens) (_ : y ∈ U) (b : B.obj.obj (Opposite.op (Etale.ofOpens V U))),
        d.hom.app _ b = (X.pointFunctionSheaf _).obj.map (Etale.ofOpensι V U).op
          (extendByZero (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (X.fromSpecResidueField x) c))
    (s : X) (a : ((X.uliftPointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      (X.pointConstantInt x)) :
    ∃ b, (X.uliftPointSmallEtale s).sheafFiber.map d b =
      (X.uliftPointSmallEtale s).sheafFiber.map (X.pointConstantIntToPointFunctionSheaf x) a := by
  let Φ := X.uliftPointSmallEtale s
  obtain ⟨V, v, t, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := (X.pointConstantInt x).obj) a
  let cf : ↥(pullback V.hom (X.fromSpecResidueField x)) → ULift.{u + 1} ℤ :=
    ((Spec (X.residueField x)).constantSheafToPointFunctionSheaf _).hom.app _ t
  have hψ : (X.pointConstantIntToPointFunctionSheaf x).hom.app (Opposite.op V) t =
      extendByZero (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (X.fromSpecResidueField x) cf := rfl
  obtain ⟨U, hyU, b, hb⟩ := hd V (v.down.left (IsLocalRing.closedPoint _)) cf
  obtain ⟨v', hv'⟩ := exists_ulift_pointSmallEtale_fiber_ofOpens _ v U
    (range_uliftPointSmallEtale_fiber_subset X v U hyU)
  refine ⟨Φ.toPresheafFiber (Etale.ofOpens V U) v' B.obj b, ?_⟩
  change Φ.presheafFiber.map d.hom _ =
    Φ.presheafFiber.map (X.pointConstantIntToPointFunctionSheaf x).hom _
  rw [Φ.toPresheafFiber_naturality_apply, Φ.toPresheafFiber_naturality_apply, hψ, hb,
    Φ.toPresheafFiber_w_apply, show Φ.fiber.map (Etale.ofOpensι V U) v' = v from hv']

omit [IsIntegral X] in
/-- **Germs in a kernel, from a local statement.** Let `f : A ⟶ B` and
`d : B ⟶ (V ↦ (V → ℤ))` be morphisms of étale sheaves. Suppose that every section of `B` over
an étale `X`-scheme `V` killed by `d` is, near every point of `V`, the image under `f` of a
section of `A`. Then on geometric stalks the kernel of `d` is contained in the image of `f`. -/
lemma exists_sheafFiber_eq_of_sheafFiber_map_eq_zero
    {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : A ⟶ B)
    (d : B ⟶ X.pointFunctionSheaf (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (hd : ∀ (V : X.Etale) (y : V.left) (b : B.obj.obj (Opposite.op V)), d.hom.app _ b = 0 →
      ∃ (U : V.left.Opens) (_ : y ∈ U) (a : A.obj.obj (Opposite.op (Etale.ofOpens V U))),
        f.hom.app _ a = B.obj.map (Etale.ofOpensι V U).op b)
    (s : X) (b : ((X.uliftPointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj B)
    (hb : (X.uliftPointSmallEtale s).sheafFiber.map d b = 0) :
    ∃ a, (X.uliftPointSmallEtale s).sheafFiber.map f a = b := by
  let Φ := X.uliftPointSmallEtale s
  obtain ⟨V, v, b₀, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := B.obj) b
  change Φ.presheafFiber.map d.hom _ = 0 at hb
  rw [Φ.toPresheafFiber_naturality_apply,
    ← map_zero (Φ.toPresheafFiber V v (X.pointFunctionSheaf _).obj).hom,
    Φ.toPresheafFiber_eq_iff'] at hb
  obtain ⟨W, φ, w, hw, hφ⟩ := hb
  have hd₀ : d.hom.app _ (B.obj.map φ.op b₀) = 0 := by
    have hnat := congrArg (fun F ↦ F b₀)
      (congrArg AddCommGrpCat.Hom.hom (d.hom.naturality φ.op))
    exact hnat.trans (hφ.trans (map_zero _))
  obtain ⟨U, hyU, a, ha⟩ := hd W (w.down.left (IsLocalRing.closedPoint _)) _ hd₀
  obtain ⟨w', hw'⟩ := exists_ulift_pointSmallEtale_fiber_ofOpens _ w U
    (range_uliftPointSmallEtale_fiber_subset X w U hyU)
  refine ⟨Φ.toPresheafFiber (Etale.ofOpens W U) w' A.obj a, ?_⟩
  change Φ.presheafFiber.map f.hom _ = _
  rw [Φ.toPresheafFiber_naturality_apply, ha, Φ.toPresheafFiber_w_apply,
    show Φ.fiber.map (Etale.ofOpensι W U) w' = w from hw', Φ.toPresheafFiber_w_apply, hw]

omit [IsIntegral X] in
/-- On geometric stalks, if the images of the point sheaves `i_{e(i)*} ℤ ⟶ (V ↦ (V → ℤ))` are
contained in that of `d`, so is the image of their direct sum. -/
lemma exists_sheafFiber_eq_desc {B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (d : B ⟶ X.pointFunctionSheaf (AddCommGrpCat.of (ULift.{u + 1} ℤ))) {ι : Type u} {e : ι → X}
    (c : Cofan fun i ↦ X.pointConstantInt (e i)) (hc : IsColimit c) (s : X)
    (hd : ∀ i (a : ((X.uliftPointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      (X.pointConstantInt (e i))), ∃ b, (X.uliftPointSmallEtale s).sheafFiber.map d b =
        (X.uliftPointSmallEtale s).sheafFiber.map (X.pointConstantIntToPointFunctionSheaf (e i)) a)
    (p : ((X.uliftPointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj c.pt) :
    ∃ b, (X.uliftPointSmallEtale s).sheafFiber.map d b =
      (X.uliftPointSmallEtale s).sheafFiber.map
        (Cofan.IsColimit.desc hc fun i ↦ X.pointConstantIntToPointFunctionSheaf (e i)) p := by
  let F := (X.uliftPointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  have hc' : IsColimit (Cofan.mk c.pt c.inj) :=
    hc.ofIsoColimit (Cofan.ext (Iso.refl _) (fun _ ↦ Category.comp_id _))
  have hd' := isColimitCofanMkObjOfIsColimit F _ c.inj hc'
  obtain ⟨T, a, rfl⟩ := AddCommGrpCat.exists_eq_sum_of_isColimit_cofan hd' p
  have hmem : F.map (Cofan.IsColimit.desc hc fun i ↦ X.pointConstantIntToPointFunctionSheaf (e i))
      (∑ i ∈ T, F.map (c.inj i) (a i)) ∈ AddMonoidHom.range (F.map d).hom := by
    rw [map_sum]
    refine AddSubgroup.sum_mem _ fun i _ ↦ ?_
    obtain ⟨b, hb⟩ := hd i (a i)
    refine ⟨b, hb.trans ?_⟩
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, Cofan.IsColimit.fac]
  obtain ⟨b, hb⟩ := hmem
  exact ⟨b, hb⟩

/-- On geometric stalks, every germ of a function on points coming from `i_{x*} ℤ` for a point
`x` of codimension one is the germ of a divisor. -/
lemma exists_sheafFiber_divisorMap_eq_pointConstantIntToPointFunctionSheaf
    [IsLocallyNoetherian X] [IsRegular X] (s : X) {x : X} (hx : coheight x = 1)
    (a : ((X.uliftPointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      (X.pointConstantInt x)) :
    ∃ b, (X.uliftPointSmallEtale s).sheafFiber.map X.divisorMap b =
      (X.uliftPointSmallEtale s).sheafFiber.map (X.pointConstantIntToPointFunctionSheaf x) a := by
  refine X.exists_sheafFiber_eq_pointConstantIntToPointFunctionSheaf _ x (fun V y c ↦ ?_) s a
  obtain ⟨U, hyU, f, hf⟩ := Etale.exists_ord_eq_extendByZero X V y hx c
  exact ⟨U, hyU, ULift.up (Additive.ofMul f), funext hf⟩

/-- On geometric stalks, a germ of a unit on the generic fibre whose divisor vanishes is the
germ of a unit. -/
lemma exists_sheafFiber_gmSheafToLowerStarGmSheaf_eq [IsLocallyNoetherian X] [IsRegular X]
    (s : X) (b : ((X.uliftPointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj
        (Spec X.functionField).gmSheaf))
    (hb : (X.uliftPointSmallEtale s).sheafFiber.map X.divisorMap b = 0) :
    ∃ a, (X.uliftPointSmallEtale s).sheafFiber.map
      (gmSheafToLowerStarGmSheaf X.fromSpecFunctionField) a = b := by
  refine X.exists_sheafFiber_eq_of_sheafFiber_map_eq_zero _ _ (fun V y b hb ↦ ?_) s b hb
  obtain ⟨U, hyU, u, hu⟩ := Etale.exists_eq_of_ord_eq_zero X V y (Additive.toMul b.down)
    (fun y' ↦ congrArg ULift.down (congrFun hb y'))
  exact ⟨U, hyU, ULift.up (Additive.ofMul u),
    ULift.ext (congrArg Additive.ofMul (Units.ext hu))⟩

/-- On geometric stalks, the image of the divisor map is contained in that of
`⨁_x i_{x*} ℤ ⟶ (V ↦ (V → ℤ))`. -/
lemma exists_sheafFiber_desc_eq_divisorMap [IsLocallyNoetherian X] [IsRegular X]
    (c : Cofan fun x : {x : X // coheight x = 1} ↦ X.pointConstantInt x.1) (hc : IsColimit c)
    (s : X) (b : ((X.uliftPointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj
        (Spec X.functionField).gmSheaf)) :
    ∃ p, (X.uliftPointSmallEtale s).sheafFiber.map
        (Cofan.IsColimit.desc hc fun x ↦ X.pointConstantIntToPointFunctionSheaf x.1) p =
      (X.uliftPointSmallEtale s).sheafFiber.map X.divisorMap b := by
  classical
  let Φ := X.uliftPointSmallEtale s
  let F := Φ.sheafFiber (A := AddCommGrpCat.{u + 1})
  let M := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  obtain ⟨V, v, f₀, rfl⟩ := Φ.toPresheafFiber_jointly_surjective
    (P := ((Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj
      (Spec X.functionField).gmSheaf).obj) b
  let y : V.left := v.down.left (IsLocalRing.closedPoint _)
  obtain ⟨U, hyU, T, hT⟩ := Etale.exists_finset_of_ord_ne_zero X V y (Additive.toMul f₀.down)
  have hU : Set.range v.down.left ⊆ (U : Set V.left) := by
    rintro _ ⟨z, rfl⟩
    have : Subsingleton (Spec (.of (AlgebraicClosure (X.residueField s)))) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum _))
    rwa [show z = IsLocalRing.closedPoint _ from @Subsingleton.elim _ this z _]
  obtain ⟨v', hv'⟩ := exists_ulift_pointSmallEtale_fiber_ofOpens _ v U hU
  let W := Etale.ofOpens V U
  -- the divisor of `f` restricted to `W`
  let D : W.left → M := (X.pointFunctionSheaf M).obj.map (Etale.ofOpensι V U).op
    (X.divisorMap.hom.app (Opposite.op V) f₀)
  let T' : Finset {x : X // coheight x = 1} := T.subtype (fun x ↦ coheight x = 1)
  have hD : D = ∑ x ∈ T', extendByZero M (X.fromSpecResidueField x.1)
      (fun z ↦ D (pullback.fst W.hom (X.fromSpecResidueField x.1) z)) := by
    funext y'
    rw [Finset.sum_apply]
    simp only [extendByZero_fromSpecResidueField_fst]
    by_cases hy' : D y' = 0
    · rw [hy']
      exact (Finset.sum_eq_zero fun x _ ↦ by split_ifs <;> rfl).symm
    · have hord : Etale.ord V (U.ι y') (Additive.toMul f₀.down).val ≠ 0 :=
        fun h ↦ hy' (ULift.ext h)
      have hcoh : coheight (W.hom y') = 1 := by
        by_contra h
        exact hord (Etale.ord_of_coheight_ne_one V h _)
      have hmem : (⟨W.hom y', hcoh⟩ : {x : X // coheight x = 1}) ∈ T' := by
        rw [Finset.mem_subtype]
        exact hT (U.ι y') ((Set.ext_iff.1 (Scheme.Opens.range_ι U) (U.ι y')).1
          (Set.mem_range_self y')) hord
      rw [Finset.sum_eq_single_of_mem _ hmem, ite_eq_left rfl]
      intro x _ hx
      rw [ite_eq_right fun h ↦ hx (Subtype.ext h.symm)]
  refine ⟨∑ x ∈ T', F.map (c.inj x) (Φ.toPresheafFiber W v' (X.pointConstantInt x.1).obj
    ((X.pointFunctionSheafToPointConstantInt x.1).hom.app (Opposite.op W) D)), ?_⟩
  have hterm (x : {x : X // coheight x = 1}) :
      F.map (Cofan.IsColimit.desc hc fun x ↦ X.pointConstantIntToPointFunctionSheaf x.1)
        (F.map (c.inj x) (Φ.toPresheafFiber W v' (X.pointConstantInt x.1).obj
          ((X.pointFunctionSheafToPointConstantInt x.1).hom.app (Opposite.op W) D))) =
      Φ.toPresheafFiber W v' (X.pointFunctionSheaf M).obj
        (extendByZero M (X.fromSpecResidueField x.1)
          (fun z ↦ D (pullback.fst W.hom (X.fromSpecResidueField x.1) z))) := by
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, Cofan.IsColimit.fac]
    change Φ.presheafFiber.map (X.pointConstantIntToPointFunctionSheaf x.1).hom _ = _
    have e : (X.pointConstantIntToPointFunctionSheaf x.1).hom.app (Opposite.op W)
        ((X.pointFunctionSheafToPointConstantInt x.1).hom.app (Opposite.op W) D) =
        extendByZero M (X.fromSpecResidueField x.1)
          (fun z ↦ D (pullback.fst W.hom (X.fromSpecResidueField x.1) z)) :=
      congrArg (fun φ ↦ (φ.hom.app (Opposite.op W)).hom D)
        (pointFunctionSheafToPointConstantInt_comp X x.1)
    rw [Φ.toPresheafFiber_naturality_apply, e]
  calc _ = ∑ x ∈ T', Φ.toPresheafFiber W v' (X.pointFunctionSheaf M).obj
        (extendByZero M (X.fromSpecResidueField x.1)
          (fun z ↦ D (pullback.fst W.hom (X.fromSpecResidueField x.1) z))) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun x _ ↦ hterm x
    _ = Φ.toPresheafFiber W v' (X.pointFunctionSheaf M).obj D := by
        rw [← map_sum, ← hD]
    _ = _ := by
        change _ = Φ.presheafFiber.map X.divisorMap.hom _
        rw [Φ.toPresheafFiber_naturality_apply,
          ← show Φ.fiber.map (Etale.ofOpensι V U) v' = v from hv', ← Φ.toPresheafFiber_w_apply]

/-- On geometric stalks, the image of `⨁_x i_{x*} ℤ ⟶ (V ↦ (V → ℤ))` is contained in that of
the divisor map. -/
lemma exists_sheafFiber_divisorMap_eq_desc [IsLocallyNoetherian X] [IsRegular X]
    (c : Cofan fun x : {x : X // coheight x = 1} ↦ X.pointConstantInt x.1) (hc : IsColimit c)
    (s : X) (p : ((X.uliftPointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj c.pt) :
    ∃ b, (X.uliftPointSmallEtale s).sheafFiber.map X.divisorMap b =
      (X.uliftPointSmallEtale s).sheafFiber.map
        (Cofan.IsColimit.desc hc fun x ↦ X.pointConstantIntToPointFunctionSheaf x.1) p :=
  exists_sheafFiber_eq_desc X _ c hc s
    (fun x ↦ X.exists_sheafFiber_divisorMap_eq_pointConstantIntToPointFunctionSheaf s x.2) p

section DivisorSequence

variable [IsLocallyNoetherian X] [IsRegular X]
  (c : Cofan fun x : {x : X // coheight x = 1} ↦ X.pointConstantInt x.1) (hc : IsColimit c)

/-- Extension by zero `⨁_{x ∈ X⁽¹⁾} i_{x*} ℤ ⟶ (V ↦ (V → ℤ))`, from the vertex of a colimit
cocone `c` on the family `x ↦ i_{x*} ℤ` to the sheaf of `ℤ`-valued functions on points: a
formal sum `∑ nₓ [x]` goes to the function which is `nₓ` on the points over `x` and `0`
elsewhere. -/
noncomputable def divisorsToPointFunctionSheaf :
    c.pt ⟶ X.pointFunctionSheaf (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  Cofan.IsColimit.desc hc fun x ↦ X.pointConstantIntToPointFunctionSheaf x.1

instance : Mono (X.divisorsToPointFunctionSheaf c hc) :=
  mono_of_injective_sheafFiber _
    (X.injective_sheafFiber_map_desc_pointConstantIntToPointFunctionSheaf Subtype.val_injective
      c hc)

/-- **The cokernel of `𝔾ₘ ⟶ i_* i^* 𝔾ₘ` is the sheaf of Weil divisors.** Let `X` be an
integral regular locally noetherian scheme with generic point `i: Spec k(X) ⟶ X`. Then the
cokernel of the unit `𝔾ₘ ⟶ i_* i^* 𝔾ₘ` is isomorphic to `⨁_{x ∈ X⁽¹⁾} i_{x*} ℤ`, the vertex
of any colimit cocone `c` on the family `x ↦ i_{x*} ℤ`, by an isomorphism induced by the
divisor map `f ↦ ∑_x ord_x(f) [x]`: composed with extension by zero
`AlgebraicGeometry.Scheme.divisorsToPointFunctionSheaf`, it is the divisor map
`AlgebraicGeometry.Scheme.divisorMap` into the sheaf of functions on points. -/
theorem exists_cokernel_toGenericGm_iso_hom_comp_eq :
    ∃ (w : X.toGenericGm ≫ X.genericGmIso.hom ≫ X.divisorMap = 0)
      (e : cokernel X.toGenericGm ≅ c.pt),
      e.hom ≫ X.divisorsToPointFunctionSheaf c hc =
        cokernel.desc _ (X.genericGmIso.hom ≫ X.divisorMap) w := by
  have := X.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField
  have he : X.toGenericGm ≫ X.genericGmIso.hom =
      gmSheafToLowerStarGmSheaf X.fromSpecFunctionField := by
    simp [genericGmIso, toGenericGm, upperStarGmSheafToGmSheaf, Adjunction.homEquiv_counit]
  have w : X.toGenericGm ≫ X.genericGmIso.hom ≫ X.divisorMap = 0 := by
    rw [← Category.assoc, he, gmSheafToLowerStarGmSheaf_comp_divisorMap]
  obtain ⟨φ, hφ⟩ := exists_cokernel_iso_hom_comp_eq_of_sheafFiber
    (gmSheafToLowerStarGmSheaf X.fromSpecFunctionField) X.divisorMap
    (X.divisorsToPointFunctionSheaf c hc)
    X.gmSheafToLowerStarGmSheaf_comp_divisorMap X.exists_sheafFiber_gmSheafToLowerStarGmSheaf_eq
    (X.injective_sheafFiber_map_desc_pointConstantIntToPointFunctionSheaf Subtype.val_injective
      c hc)
    (X.exists_sheafFiber_desc_eq_divisorMap c hc) (X.exists_sheafFiber_divisorMap_eq_desc c hc)
  refine ⟨w, (cokernelCompIsIso _ _).symm ≪≫ cokernelIsoOfEq he ≪≫ φ, ?_⟩
  refine coequalizer.hom_ext ?_
  simp [hφ]

/-- **The divisor map** `div : i_* i^* 𝔾ₘ ⟶ ⨁_{x ∈ X⁽¹⁾} i_{x*} ℤ` of an integral regular
locally noetherian scheme `X`, where the target is the vertex of a colimit cocone `c` on the
family `x ↦ i_{x*} ℤ`. It sends a rational function `f` to its divisor
`∑_{x ∈ X⁽¹⁾} ord_x(f) [x]`, i.e. it lifts `AlgebraicGeometry.Scheme.divisorMap` along
extension by zero `AlgebraicGeometry.Scheme.divisorsToPointFunctionSheaf`. -/
noncomputable def divisorSequenceMap : X.genericGm ⟶ c.pt :=
  Abelian.monoLift (X.divisorsToPointFunctionSheaf c hc) (X.genericGmIso.hom ≫ X.divisorMap) (by
    obtain ⟨w, e, he⟩ := X.exists_cokernel_toGenericGm_iso_hom_comp_eq c hc
    rw [← cokernel.π_desc X.toGenericGm _ w, ← he, Category.assoc, Category.assoc,
      cokernel.condition, comp_zero, comp_zero])

/-- The divisor map `AlgebraicGeometry.Scheme.divisorSequenceMap`, followed by extension by
zero, is `f ↦ (y ↦ ord_y(f))`. -/
@[reassoc (attr := simp)]
lemma divisorSequenceMap_comp :
    X.divisorSequenceMap c hc ≫ X.divisorsToPointFunctionSheaf c hc =
      X.genericGmIso.hom ≫ X.divisorMap :=
  Abelian.monoLift_comp _ _ _

lemma toGenericGm_comp_divisorSequenceMap :
    X.toGenericGm ≫ X.divisorSequenceMap c hc = 0 := by
  obtain ⟨w, -, -⟩ := X.exists_cokernel_toGenericGm_iso_hom_comp_eq c hc
  rw [← cancel_mono (X.divisorsToPointFunctionSheaf c hc), Category.assoc,
    divisorSequenceMap_comp, w, zero_comp]

/-- **The divisor sequence.** Let `X` be an integral regular locally noetherian scheme with
generic point `i: Spec k(X) ⟶ X`, and let `X⁽¹⁾` be its set of coheight-one points. Then

```
  0 ──▶ 𝔾ₘ ──unit──▶ i_* i^* 𝔾ₘ ──div──▶ ∐_{x ∈ X⁽¹⁾} i_{x*} ℤ ──▶ 0
```

is a short exact sequence of étale sheaves on `X`, where the third term is the vertex of any
colimit cocone `c` on the family `x ↦ i_{x*} ℤ`, the first map is the unit
`AlgebraicGeometry.Scheme.toGenericGm` and `div` is the divisor map
`AlgebraicGeometry.Scheme.divisorSequenceMap`, `f ↦ ∑_x ord_x(f) [x]`. -/
theorem shortExact_divisorSequence :
    (ShortComplex.mk X.toGenericGm (X.divisorSequenceMap c hc)
      (X.toGenericGm_comp_divisorSequenceMap c hc)).ShortExact := by
  have := X.mono_toGenericGm
  obtain ⟨w, e, he⟩ := X.exists_cokernel_toGenericGm_iso_hom_comp_eq c hc
  have hd : X.divisorSequenceMap c hc = cokernel.π _ ≫ e.hom := by
    rw [← cancel_mono (X.divisorsToPointFunctionSheaf c hc), divisorSequenceMap_comp,
      Category.assoc, he, cokernel.π_desc]
  have : Epi (X.divisorSequenceMap c hc) := by rw [hd]; exact epi_comp _ _
  refine { mono_f := ‹_›, epi_g := this, exact := ?_ }
  exact ShortComplex.exact_of_g_is_cokernel _
    (IsColimit.ofIsoColimit (cokernelIsCokernel _) (Cofork.ext e hd.symm))

include hc in
/-- **The cokernel of `𝔾ₘ ⟶ i_* i^* 𝔾ₘ` is the sheaf of Weil divisors**, as an isomorphism
`cokernel (𝔾ₘ ⟶ i_* i^* 𝔾ₘ) ≅ ⨁_{x ∈ X⁽¹⁾} i_{x*} ℤ`; see
`AlgebraicGeometry.Scheme.exists_cokernel_toGenericGm_iso_hom_comp_eq` for its compatibility
with the divisor map. -/
theorem nonempty_cokernel_toGenericGm_iso : Nonempty (cokernel X.toGenericGm ≅ c.pt) :=
  let ⟨_, e, _⟩ := X.exists_cokernel_toGenericGm_iso_hom_comp_eq c hc
  ⟨e⟩

include hc in
/-- The divisor sequence of `AlgebraicGeometry.Scheme.shortExact_divisorSequence`, with the
divisor map forgotten. -/
theorem exists_shortExact_divisorSequence :
    ∃ (d : X.genericGm ⟶ c.pt) (w : X.toGenericGm ≫ d = 0),
      (ShortComplex.mk X.toGenericGm d w).ShortExact :=
  ⟨_, _, X.shortExact_divisorSequence c hc⟩

end DivisorSequence

omit [IsIntegral X] in
/-- **`H¹` of a point sheaf vanishes.** For a point `x` of `X`, `H¹(X, i_{x*} ℤ) = 0`. -/
theorem subsingleton_H_one_pointConstantInt (x : X) :
    Subsingleton (Sheaf.H (X.pointConstantInt x) 1) := by
  have h := Etale.injective_edgeMap_one (X.fromSpecResidueField x)
    ((constantSheaf _ AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ)))
  have := subsingleton_H_one_constantSheaf_of_isField (X.residueField x) (Field.toIsField _)
  exact ⟨fun a b ↦ h (this.elim _ _)⟩

/-- **`R¹i_* 𝔾ₘ = 0` along the generic point.** Let `X` be an integral regular noetherian
scheme with generic point `i : Spec k(X) ⟶ X`. Then the first higher direct image
`R¹i_*(i^* 𝔾ₘ)` vanishes; here this is phrased as: for every monomorphism `ι : i^* 𝔾ₘ ⟶ I` into
an injective sheaf, `i_*` maps the cokernel map of `ι` to an epimorphism (so that
`0 ⟶ i_* i^* 𝔾ₘ ⟶ i_* I ⟶ i_* (I / i^* 𝔾ₘ) ⟶ 0` is exact and `R¹i_*(i^* 𝔾ₘ)`, its obstruction,
is zero). -/
theorem epi_lowerStar_map_cokernelπ_upperStar_gmSheaf [IsNoetherian X] [IsRegular X]
    {I : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ι : (Etale.upperStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj X.gmSheaf ⟶ I)
    [Mono ι] [Injective I] :
    Epi ((Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).map (cokernel.π ι)) := by
  have := X.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField
  let g := upperStarGmSheafToGmSheaf X.fromSpecFunctionField
  -- the sequence `0 → 𝔾ₘ → I → I / 𝔾ₘ → 0` on the small étale site of `Spec k(X)`
  let ι' := inv g ≫ ι
  have w : ι' ≫ cokernel.π ι = 0 := by simp [ι']
  have hS : (ShortComplex.mk ι' (cokernel.π ι) w).ShortExact :=
    ShortComplex.shortExact_of_iso (S₁ := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι))
      (ShortComplex.isoMk (asIso g) (Iso.refl _) (Iso.refl _) (by simp [ι']) (by simp))
      (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel ι) inferInstance inferInstance)
  have : QuasiCompact X.fromSpecFunctionField := quasiCompact_of_compactSpace _
  refine (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u + 1})
    ((Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).map (cokernel.π ι))).1
    ⟨fun {U} s ↦ X.smallEtaleTopology.superset_covering ?_
    ((ofArrows_mem_smallEtaleTopology_iff
      (fun V : U.left.affineOpens ↦ Etale.ofOpensι U V.1)).2 ?_)⟩
  · -- over an affine open `V` of `U`, the section lifts by Hilbert 90 on the generic fibre
    refine (Sieve.generate_le_iff _ _).2 fun _ _ ⟨V⟩ ↦ ?_
    have : CompactSpace (Etale.ofOpens U V.1).left := by
      have : IsAffine V.1.toScheme := V.2
      exact inferInstanceAs (CompactSpace V.1.toScheme)
    have : CompactSpace ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
        X.fromSpecFunctionField).obj (Etale.ofOpens U V.1)).left :=
      @QuasiCompact.compactSpace_of_compactSpace _ _
        (Limits.pullback.fst (Etale.ofOpens U V.1).hom X.fromSpecFunctionField) inferInstance this
    exact surjective_app_of_shortExact_gmSheaf_of_compactSpace ι' (cokernel.π ι) w hS
      ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ X.fromSpecFunctionField).obj
        (Etale.ofOpens U V.1)) _
  · -- the affine opens cover `U`
    refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨V, hV, hxV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1
      (isBasis_affineOpens U.left) (show x ∈ (⊤ : U.left.Opens) from trivial)
    refine Set.mem_iUnion.2 ⟨⟨V, hV⟩, ?_⟩
    change x ∈ Set.range (Scheme.Opens.ι (X := U.left) V)
    rw [Scheme.Opens.range_ι]
    exact hxV

/-- **Grothendieck's residue injection for the Brauer group.** Let `X` be an integral regular
noetherian scheme with function field `k(X)`. Then the pullback along the generic point
`i: Spec k(X) ⟶ X`

```
   Spec k(X) ──── i ────▶ X            H²(X_ét, 𝔾ₘ)
                                            │ cohomologyMap i 𝔾ₘ 2
                                            ▼
                                       H²(Spec k(X)_ét, i^* 𝔾ₘ)
```

is injective, that is, `Br(X) = H²(X, 𝔾ₘ) ↪ H²(Spec k(X), 𝔾ₘ) = Br(k(X))`. -/
theorem injective_cohomologyMap_gmSheaf_two [IsNoetherian X] [IsRegular X] :
    Function.Injective (Etale.cohomologyMap X.fromSpecFunctionField X.gmSheaf 2) := by
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{u, u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  let P := fun x : {x : X // coheight x = 1} ↦ X.pointConstantInt x.1
  have hS := X.shortExact_divisorSequence (colimit.cocone (Discrete.functor P))
    (colimit.isColimit _)
  -- the unit `𝔾ₘ ⟶ i_* i^* 𝔾ₘ` is injective on `H²`, as `H¹(X, ⨁_x i_{x*} ℤ) = 0`
  have h₃ : Subsingleton (Sheaf.H (colimit.cocone (Discrete.functor P)).pt 1) :=
    subsingleton_H_one_of_isColimit_cofan X (colimit.isColimit _)
      fun x ↦ X.subsingleton_H_one_pointConstantInt x.1
  have hα : Function.Injective (Sheaf.H.map X.toGenericGm 2) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    rw [Sheaf.H.map_apply] at ha
    obtain ⟨b, rfl⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS a ha (n₀ := 1) rfl
    rw [Subsingleton.elim b 0, Abelian.Ext.zero_comp]
  -- the edge map `H²(X, i_* i^* 𝔾ₘ) ⟶ H²(Spec k(X), i^* 𝔾ₘ)` is injective
  let ι := Injective.ι ((Etale.upperStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj
    X.gmSheaf)
  have hβ := Etale.injective_edgeMap_two X.fromSpecFunctionField ι
    (X.epi_lowerStar_map_cokernelπ_upperStar_gmSheaf ι)
  intro a b h
  rw [Etale.cohomologyMap_eq_map_counit_comp, Etale.cohomologyMap_eq_map_counit_comp _ _ _ b] at h
  exact hα (hβ h)

end AlgebraicGeometry.Scheme
