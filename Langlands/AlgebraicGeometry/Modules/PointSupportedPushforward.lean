import Langlands.AlgebraicGeometry.Modules.PointSupportedSkyscraper
import Langlands.AlgebraicGeometry.Modules.AffineHigherDirectImageSections
import Langlands.AlgebraicGeometry.Modules.StalkPullback
import Langlands.AlgebraicGeometry.Modules.StalkTrivialization
import Langlands.AlgebraicGeometry.Modules.Tensor

/-! # Recognizing modules supported at one closed point from their sections over an affine open -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

section Germ

variable {Y : Scheme.{u}} {V : Y.Opens} (hV : IsAffineOpen V)

/-- A point of `V` lies in the open of `Y` over which the affine sections are taken. -/
lemma mem_image_preimage_top {y : Y} (hy : y ∈ V) : y ∈ V.ι ''ᵁ (hV.isoSpec.hom ⁻¹ᵁ ⊤) :=
  ⟨⟨y, hy⟩, trivial, rfl⟩

/-- The germ at a point of `V` of an affine section. -/
def affineSectionsGerm (N : Y.Modules) {y : Y} (hy : y ∈ V) :
    affineSections hV N →+ stalk N y :=
  (N.presheaf.germ (V.ι ''ᵁ (hV.isoSpec.hom ⁻¹ᵁ ⊤)) y (mem_image_preimage_top hV hy)).hom

/-- The germ of affine sections is linear over the germ of functions on `V`. -/
lemma affineSectionsGerm_smul (N : Y.Modules) {y : Y} (hy : y ∈ V) (r : Γ(Y, V))
    (m : affineSections hV N) :
    affineSectionsGerm hV N hy (r • m) =
      Y.presheaf.germ V y hy r • affineSectionsGerm hV N hy m := by
  let a0 : Γ(V.toScheme, hV.isoSpec.hom ⁻¹ᵁ ⊤) :=
    hV.isoSpec.hom.appTop ((Scheme.ΓSpecIso Γ(Y, V)).inv r)
  have h1 : (r • m : affineSections hV N) =
      (a0 • (show Γ(N.restrict V.ι, hV.isoSpec.hom ⁻¹ᵁ ⊤) from m) :
        Γ(N.restrict V.ι, hV.isoSpec.hom ⁻¹ᵁ ⊤)) := rfl
  have h2 := Scheme.Modules.smul_restrictAppIso_hom_apply (f := V.ι) N (hV.isoSpec.hom ⁻¹ᵁ ⊤) a0 m
  have h3 : (r • m : affineSections hV N) =
      ((V.ι.appIso (hV.isoSpec.hom ⁻¹ᵁ ⊤)).inv a0 •
        (show Γ(N, V.ι ''ᵁ (hV.isoSpec.hom ⁻¹ᵁ ⊤)) from m) :
        Γ(N, V.ι ''ᵁ (hV.isoSpec.hom ⁻¹ᵁ ⊤))) := by
    rw [h1]
    exact h2
  unfold affineSectionsGerm
  rw [h3]
  erw [PresheafOfModules.germ_smul]
  congr 1
  simp only [a0, Scheme.Opens.ι_appIso, Iso.refl_inv, IsAffineOpen.isoSpec_hom_appTop,
    Scheme.Opens.topIso_inv, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  exact Y.presheaf.germ_res_apply _ y _ r

/-- A module whose stalk support lies in a closed point `y` of an affine open `V` vanishes as soon
as its sections over `V` vanish. -/
theorem isZero_of_isZero_affineSections {y : Y} (hy : y ∈ V) (hcl : IsClosed ({y} : Set Y))
    (N : Y.Modules) (hN : stalkSupport N ⊆ {y}) (h : IsZero (affineSections hV N)) : IsZero N := by
  rw [← stalkSupport_eq_empty_iff]
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  have hxy : x = y := hN hx
  subst hxy
  have hsub : Subsingleton (affineSections hV N) := ModuleCat.isZero_iff_subsingleton.1 h
  have hbij := StalkAdjunction.germ_bijective_of_stalkSupport_subset hcl N hN _
    (mem_image_preimage_top hV hy)
  rw [mem_stalkSupport_iff_nontrivial] at hx
  obtain ⟨a, b, hab⟩ := hx
  obtain ⟨a', rfl⟩ := hbij.2 a
  obtain ⟨b', rfl⟩ := hbij.2 b
  exact hab (congrArg _ (@Subsingleton.elim _ hsub a' b'))

end Germ

section Localization

variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Submonoid R)
  [IsLocalization S A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- An additive equivalence between modules over a localization `A` of `R` which commutes with
the action of `R` through `algebraMap R A` is `A`-linear. -/
def linearEquivOfIsLocalization (f : M ≃+ N)
    (hf : ∀ (r : R) (m : M), f (algebraMap R A r • m) = algebraMap R A r • f m) :
    M ≃ₗ[A] N :=
  letI : Module R M := Module.compHom M (algebraMap R A)
  letI : Module R N := Module.compHom N (algebraMap R A)
  haveI : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  LinearEquiv.extendScalarsOfIsLocalization S A { f with map_smul' := hf }

end Localization

section FieldPoint

variable {k : Type u} [Field k] (pt : Spec (CommRingCat.of k))

/-- Every germ at the point of the spectrum of a field comes from a global function. -/
lemma germ_top_surjective_of_field :
    Function.Surjective ((Spec (CommRingCat.of k)).presheaf.germ ⊤ pt trivial) := by
  intro z
  obtain ⟨U, hU, a, rfl⟩ := (Spec (CommRingCat.of k)).presheaf.exists_germ_eq z
  have hU' : (⊤ : (Spec (CommRingCat.of k)).Opens) ≤ U := by
    intro p _
    rw [Subsingleton.elim p pt]
    exact hU
  exact ⟨(Spec (CommRingCat.of k)).presheaf.map (homOfLE hU').op a,
    (Spec (CommRingCat.of k)).presheaf.germ_res_apply (homOfLE hU') pt trivial a⟩

/-- In the local ring at the point of the spectrum of a field, every nonunit is zero. -/
lemma eq_zero_of_not_isUnit_stalk_of_field (z : (Spec (CommRingCat.of k)).presheaf.stalk pt)
    (hz : ¬ IsUnit z) : z = 0 := by
  obtain ⟨a, rfl⟩ := germ_top_surjective_of_field pt z
  by_cases ha : a = 0
  · rw [ha, map_zero]
  · exfalso
    apply hz
    have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of k)).hom a) := by
      refine isUnit_iff_ne_zero.2 fun h0 => ha ?_
      rw [← Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of k)) a, h0, map_zero]
    have hu' := hu.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    rw [Iso.hom_inv_id_apply] at hu'
    exact hu'.map _

variable {Y : Scheme.{u}} (i : Spec (CommRingCat.of k) ⟶ Y) {V : Y.Opens} (hy : i pt ∈ V)

/-- Evaluation of functions on `V` at the point `i pt`, through the stalk map of `i`. -/
def pointEval : Γ(Y, V) →+* (Spec (CommRingCat.of k)).presheaf.stalk pt :=
  (i.stalkMap pt).hom.comp (Y.presheaf.germ V (i pt) hy).hom

lemma pointEval_apply (r : Γ(Y, V)) :
    pointEval pt i hy r = i.stalkMap pt (Y.presheaf.germ V (i pt) hy r) := rfl

/-- The kernel of evaluation at `i pt` is the prime ideal of `i pt` in `Γ(Y, V)`. -/
lemma pointEval_eq_zero_iff (hV : IsAffineOpen V) (r : Γ(Y, V)) :
    pointEval pt i hy r = 0 ↔ r ∈ (hV.primeIdealOf ⟨i pt, hy⟩).asIdeal := by
  let := Y.presheaf.algebra_section_stalk ⟨i pt, hy⟩
  have := hV.isLocalization_stalk ⟨i pt, hy⟩
  have key := IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk (i pt))
    (hV.primeIdealOf ⟨i pt, hy⟩).asIdeal r
  constructor
  · intro h0
    by_contra hr
    have hu : IsUnit (Y.presheaf.germ V (i pt) hy r) := key.2 hr
    have hu' := hu.map (i.stalkMap pt).hom
    rw [← pointEval_apply, h0] at hu'
    exact not_isUnit_zero hu'
  · intro hr
    apply eq_zero_of_not_isUnit_stalk_of_field
    intro hu
    rw [pointEval_apply] at hu
    exact key.1 ((isUnit_map_iff (i.stalkMap pt).hom _).1 hu) hr

/-- Evaluation at `i pt` is surjective when `i` has a retraction. -/
lemma pointEval_surjective (s : Y ⟶ Spec (CommRingCat.of k)) (his : i ≫ s = 𝟙 _) :
    Function.Surjective (pointEval pt i hy) := by
  intro z
  obtain ⟨c, rfl⟩ := germ_top_surjective_of_field pt z
  refine ⟨Y.presheaf.map (homOfLE le_top).op (s.appTop c), ?_⟩
  have hgen : ∀ f : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k), f = 𝟙 _ →
      (Spec (CommRingCat.of k)).presheaf.germ (f ⁻¹ᵁ ⊤) pt trivial (f.appTop c) =
        (Spec (CommRingCat.of k)).presheaf.germ ⊤ pt trivial c := by
    rintro f rfl
    rfl
  rw [← hgen (i ≫ s) his, pointEval_apply, Y.presheaf.germ_res_apply]
  erw [i.germ_stalkMap_apply]
  rfl

end FieldPoint

section PushforwardRecognition

variable {k : Type u} [Field k] (pt : Spec (CommRingCat.of k))
  {Y : Scheme.{u}} (i : Spec (CommRingCat.of k) ⟶ Y) (s : Y ⟶ Spec (CommRingCat.of k))
  (his : i ≫ s = 𝟙 _) {V : Y.Opens} (hV : IsAffineOpen V) (hy : i pt ∈ V)

include his

/-- The residue ring of `Γ(Y, V)` at `i pt` is the local ring of the point, through evaluation
at `i pt`. -/
def quotientPointEquiv :
    (Γ(Y, V) ⧸ (hV.primeIdealOf ⟨i pt, hy⟩).asIdeal) ≃+*
      (Spec (CommRingCat.of k)).presheaf.stalk pt :=
  (Ideal.quotEquivOfEq (Ideal.ext fun r =>
      (pointEval_eq_zero_iff pt i hy hV r).symm.trans RingHom.mem_ker.symm)).trans
    (RingHom.quotientKerEquivOfSurjective (pointEval_surjective pt i hy s his))

lemma quotientPointEquiv_mk (r : Γ(Y, V)) :
    quotientPointEquiv pt i s his hV hy (Ideal.Quotient.mk _ r) = pointEval pt i hy r := by
  rw [quotientPointEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- If the sections over `V` of a module `N` supported at the closed point `i pt` form the
residue ring of `Γ(Y, V)` at `i pt`, then the stalk of `N` at `i pt` is the stalk of the
structure sheaf of the point, with scalars restricted along the stalk map of `i`. -/
theorem nonempty_stalk_iso_of_affineSections_iso (N : Y.Modules)
    (hcl : IsClosed ({i pt} : Set Y)) (hN : stalkSupport N ⊆ {i pt})
    (e : affineSections hV N ≅
      ModuleCat.of Γ(Y, V) (Γ(Y, V) ⧸ (hV.primeIdealOf ⟨i pt, hy⟩).asIdeal)) :
    Nonempty ((stalkFunctor (i pt)).obj N ≅
      (ModuleCat.restrictScalars (i.stalkMap pt).hom).obj
        ((stalkFunctor pt).obj (SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf))) := by
  let := Y.presheaf.algebra_section_stalk ⟨i pt, hy⟩
  have := hV.isLocalization_stalk ⟨i pt, hy⟩
  let B := (ModuleCat.restrictScalars (i.stalkMap pt).hom).obj
    ((stalkFunctor pt).obj (SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf))
  let G : affineSections hV N ≃+ stalk N (i pt) :=
    AddEquiv.ofBijective (affineSectionsGerm hV N hy)
      (StalkAdjunction.germ_bijective_of_stalkSupport_subset hcl N hN _
        (mem_image_preimage_top hV hy))
  let u := unitStalkLinearEquiv (Spec (CommRingCat.of k)) pt
  let q := quotientPointEquiv pt i s his hV hy
  have hq : ∀ r, q (Ideal.Quotient.mk _ r) = pointEval pt i hy r :=
    quotientPointEquiv_mk pt i s his hV hy
  let f : stalk N (i pt) ≃+ B :=
    G.symm.trans (e.toLinearEquiv.toAddEquiv.trans (q.toAddEquiv.trans u.symm.toAddEquiv))
  have hfG : ∀ x, f (G x) = u.symm (q (e.hom x)) := by
    intro x
    change u.symm (q (e.toLinearEquiv (G.symm (G x)))) = _
    rw [G.symm_apply_apply]
    rfl
  refine ⟨(linearEquivOfIsLocalization (hV.primeIdealOf ⟨i pt, hy⟩).asIdeal.primeCompl f
    ?_).toModuleIso⟩
  intro r a
  obtain ⟨m, rfl⟩ := G.surjective a
  have hG : algebraMap Γ(Y, V) (Y.presheaf.stalk (i pt)) r • G m = G (r • m) :=
    (affineSectionsGerm_smul hV N hy r m).symm
  rw [hG, hfG, hfG]
  have h1 : e.hom (r • m) = r • e.hom m := e.hom.hom.map_smul r m
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (e.hom m)
  rw [h1, ← ht]
  change u.symm (q (Ideal.Quotient.mk _ (r * t))) = pointEval pt i hy r • u.symm (q _)
  rw [map_mul, map_mul, hq, hq]
  exact u.symm.map_smul (pointEval pt i hy r) (pointEval pt i hy t)

/-- A module on `Y` supported at the closed point `i pt`, whose sections over an affine open
`V ∋ i pt` form the residue ring of `Γ(Y, V)` at `i pt`, is the pushforward along `i` of the
structure sheaf of the point. -/
theorem nonempty_iso_pushforward_of_affineSections_iso (N : Y.Modules)
    (hcl : IsClosed ({i pt} : Set Y)) (hN : stalkSupport N ⊆ {i pt})
    (e : affineSections hV N ≅
      ModuleCat.of Γ(Y, V) (Γ(Y, V) ⧸ (hV.primeIdealOf ⟨i pt, hy⟩).asIdeal)) :
    Nonempty (N ≅ (Scheme.Modules.pushforward i).obj
      (Langlands.Scheme.Modules.structureSheaf (Spec (CommRingCat.of k)))) := by
  obtain ⟨φ⟩ := nonempty_stalk_iso_of_affineSections_iso pt i s his hV hy N hcl hN e
  have hpt : IsClosed ({pt} : Set (Spec (CommRingCat.of k))) := by
    have : ({pt} : Set (Spec (CommRingCat.of k))) = Set.univ :=
      Set.eq_univ_of_forall fun p => Subsingleton.elim p pt
    rw [this]
    exact isClosed_univ
  have hsupp : stalkSupport (SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf) ⊆
      {pt} := fun p _ => Subsingleton.elim p pt
  exact ⟨StalkAdjunction.isoSkyscraperOfStalkSupportSubset hcl N hN ≪≫
    (StalkAdjunction.skyscraperFunctor (i pt)).mapIso φ ≪≫
    ((StalkPullback.skyscraperPushforwardIso i pt).app _).symm ≪≫
    (Scheme.Modules.pushforward i).mapIso
      (StalkAdjunction.isoSkyscraperOfStalkSupportSubset hpt _ hsupp).symm⟩

end PushforwardRecognition

end Langlands.AlgebraicGeometry.Modules.DerivedSections
