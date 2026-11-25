import Langlands.AlgebraicGeometry.ArtinianLiftingSmooth
import Langlands.GroupScheme.HomScheme.ArtinianTorusCentralizerLift
import Langlands.GroupScheme.HomScheme.SubgroupFamilyEvaluation
import Langlands.GroupScheme.Reductive.GenericFiberGeometry

/-! # Smoothness of a torus centralizer parameter scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor

private theorem range_comp_iso_eq_centralizer_iff {S : Scheme.{u}}
    {X Y H T : GroupScheme S} (e : X ≅ Y) (j : H ⟶ X) (t : T ⟶ X) :
    range (j ≫ e.hom) = (range (t ≫ e.hom)).centralizer ↔
      range j = (range t).centralizer := by
  have ht : (range (t ≫ e.hom)).centralizer = (range t).centralizer.comap e.inv := by
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      centralizer_range_eq_comap_of_iso (t ≫ e.hom) e.symm
  rw [range_comp_iso, ht]
  constructor
  · intro h
    have he := congrArg (comap e.hom) h
    simpa only [← comap_comp, Iso.hom_inv_id, comap_id] using he
  · intro h
    rw [h]

private theorem evaluate_eq_centralizer {S : Scheme.{u}} {G : GroupScheme S}
    {U V : Over S} {H T : GroupScheme U.left}
    (i : H ⟶ (baseChange U.hom).obj G) (t : T ⟶ (baseChange U.hom).obj G)
    (h : range i = (range t).centralizer) (a : V ⟶ U) :
    evaluate i a = (evaluate t a).centralizer := by
  apply (range_comp_iso_eq_centralizer_iff
    (Descent.pullbackComparison U.hom a.left V.hom a.w G) _ _).mpr
  rw [range_baseChangeHom, range_baseChangeHom, h, SubgroupFunctor.centralizer_baseChange]

/-- A subgroup functor is the centralizer of an actual closed torus. -/
def IsTorusCentralizer {S : Scheme.{u}} {G : GroupScheme S} (F : SubgroupFunctor G) : Prop :=
  ∃ (T : GroupScheme S) (t : T ⟶ G), IsClosedSubgroup t ∧ RelativeTorus.IsTorus T ∧
    F = (range t).centralizer

/-- The actual fibres of the inclusion over the residue fields of its base
are the centralizers of closed tori. -/
def HasTorusCentralizerResidueFibres {S : Scheme.{u}} {G H : GroupScheme S}
    (i : H ⟶ G) : Prop :=
  ∀ s : S, IsTorusCentralizer (range ((baseChange (S.fromSpecResidueField s)).map i))

private theorem isTorusCentralizer_evaluate_of_baseChange {S : Scheme.{u}} {G : GroupScheme S}
    {U M : Over S} {H : GroupScheme M.left} (c : H ⟶ (baseChange M.hom).obj G)
    (a : U ⟶ M) (h : IsTorusCentralizer (range ((baseChange a.left).map c))) :
    IsTorusCentralizer (evaluate c a) := by
  obtain ⟨T, t, ht, hT, he⟩ := h
  let e := Descent.pullbackComparison M.hom a.left U.hom a.w G
  have ht' : IsClosedSubgroup (t ≫ e.hom) := by
    have : IsClosedImmersion t.hom.hom.left := ht
    change IsClosedImmersion (t.hom.hom.left ≫ e.hom.hom.hom.left)
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
    infer_instance
  have hh := (range_comp_iso_eq_centralizer_iff e ((baseChange a.left).map c) t).mpr he
  exact ⟨T, t ≫ e.hom, ht', hT, hh⟩

private theorem isTorusCentralizer_evaluate_comp {S : Scheme.{u}} {G : GroupScheme S}
    {U V M : Over S} {H : GroupScheme M.left} (c : H ⟶ (baseChange M.hom).obj G)
    (a : U ⟶ M) (b : V ⟶ U) (h : IsTorusCentralizer (evaluate c a)) :
    IsTorusCentralizer (evaluate c (b ≫ a)) := by
  obtain ⟨T, t, ht, hT, he⟩ := h
  rw [← evaluate_comp]
  exact ⟨_, familyHom t b, isClosedSubgroup_familyHom t ht b, hT.baseChange b.left,
    evaluate_eq_centralizer (familyHom c a) t he b⟩

private theorem isTorusCentralizer_evaluate_field {S : Scheme.{u}} {G : GroupScheme S}
    {M : Over S} {H : GroupScheme M.left} (c : H ⟶ (baseChange M.hom).obj G)
    (hc : HasTorusCentralizerResidueFibres c)
    {k : Type u} [Field k] (f : Spec (CommRingCat.of k) ⟶ S) (a : Over.mk f ⟶ M) :
    IsTorusCentralizer (evaluate c a) := by
  let s := a.left (closedPoint k)
  let r := M.left.fromSpecResidueField s
  let p := Spec.map (fieldPointResidueMap a.left)
  have hp : p ≫ r = a.left := fieldPointResidueMap_factorization a.left
  let V := Over.mk (r ≫ M.hom)
  let b : V ⟶ M := Over.homMk r rfl
  let d : Over.mk f ⟶ V := Over.homMk p (by
    change p ≫ (r ≫ M.hom) = f
    rw [← Category.assoc, hp]
    exact a.w)
  have hda : d ≫ b = a := Over.OverMorphism.ext hp
  have hb := isTorusCentralizer_evaluate_of_baseChange c b (hc s)
  exact hda ▸ isTorusCentralizer_evaluate_comp c b d hb

section Quotient

variable {S : Scheme.{u}} {G : GroupScheme S} {M : Over S} {H : GroupScheme M.left}
variable (c : H ⟶ (baseChange M.hom).obj G) [Smooth H.X.hom]
variable (hc : IsClosedSubgroup c) (hF : HasTorusCentralizerResidueFibres c)
variable (hU : ∀ (U : Over S) (F : SubgroupFunctor ((baseChange U.hom).obj G)),
  IsAdmissible F → ∃! a : U ⟶ M, evaluate c a = F.centralizer)
variable {A : Type u} [CommRing A] [IsLocalRing A] (I : Ideal A)
variable [IsLocalRing (A ⧸ I)] [IsArtinianRing (A ⧸ I)]
variable (f : Spec (CommRingCat.of A) ⟶ S)

local notation "q" => Spec.algebraMap A (A ⧸ I)

include c hc hF hU in
set_option maxHeartbeats 1200000 in
private theorem exists_lift_over_quotient (hI : IsNilpotent I)
    [Smooth ((baseChange f).obj G).X.hom] [IsAffineHom ((baseChange f).obj G).X.hom]
    [Smooth ((baseChange (Over.mk (q ≫ f)).hom).obj G).X.hom]
    [IsAffineHom ((baseChange (Over.mk (q ≫ f)).hom).obj G).X.hom]
    (a₀ : Over.mk (q ≫ f) ⟶ M) :
    ∃ a : Over.mk f ⟶ M, (Over.homMk q rfl : Over.mk (q ≫ f) ⟶ Over.mk f) ≫ a = a₀ := by
  let W := Over.mk f
  let U := Over.mk (q ≫ f)
  let b : U ⟶ W := Over.homMk q rfl
  let C := (baseChange a₀.left).obj H
  let j := familyHom c a₀
  have hj : IsClosedSubgroup j := isClosedSubgroup_familyHom c hc a₀
  have : Smooth C.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  let e := Descent.pullbackComparison W.hom b.left U.hom b.w G
  let K := A ⧸ I
  let q₀ := Spec.algebraMap K (K ⧸ maximalIdeal K)
  let V := Over.mk (q₀ ≫ U.hom)
  let b₀ : V ⟶ U := Over.homMk q₀ rfl
  let e₀ := Descent.pullbackComparison U.hom b₀.left V.hom b₀.w G
  obtain ⟨T₀, t₀, ht₀, hT₀, he₀⟩ :=
    isTorusCentralizer_evaluate_field c hF (k := ResidueField K) V.hom (b₀ ≫ a₀)
  let t₀' := t₀ ≫ e₀.inv
  have ht₀' : IsClosedSubgroup t₀' := by
    have : IsClosedImmersion t₀.hom.hom.left := ht₀
    change IsClosedImmersion (t₀.hom.hom.left ≫ e₀.inv.hom.hom.left)
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
    infer_instance
  have heT : t₀' ≫ e₀.hom = t₀ := by simp [t₀']
  have hj₀ : range ((baseChange q₀).map j) = (range t₀').centralizer := by
    apply (range_comp_iso_eq_centralizer_iff e₀ _ _).mp
    rw [heT]
    change evaluate j b₀ = _
    rw [evaluate_comp]
    exact he₀
  obtain ⟨T, t, ht, hT, heq⟩ := exists_torus_of_isCentralizer_closedFiber j hj t₀' ht₀' hT₀ hj₀
  let t' := t ≫ e.inv
  have ht' : IsClosedSubgroup t' := by
    have : IsClosedImmersion t.hom.hom.left := ht
    change IsClosedImmersion (t.hom.hom.left ≫ e.inv.hom.hom.left)
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
    infer_instance
  obtain ⟨L, l, hl, hL, hred⟩ := exists_closedTorus_lift_of_affine I hI
    ((baseChange f).obj G) (range t') (isAdmissible_range t' ht' hT)
  obtain ⟨a, ha, -⟩ := hU W (range l) (isAdmissible_range l hl hL)
  have htr : evaluate l b = range t := by
    change range ((baseChange q).map l ≫ e.hom) = _
    rw [range_postcomp_congr _ t' _ hred]
    simp [t']
  have hba : evaluate c (b ≫ a) = (range t).centralizer := by
    rw [← evaluate_comp, evaluate_eq_centralizer (familyHom c a) l ha, htr]
  obtain ⟨a', _, huniq⟩ := hU U (range t) (isAdmissible_range t ht hT)
  exact ⟨a, (huniq _ hba).trans (huniq _ heq).symm⟩

end Quotient

/-- A locally finite-type parameter scheme of actual torus centralizers is
smooth when the ambient group is smooth and becomes affine on local Artinian
tests, and its smooth closed universal family has torus-centralizer residue
fibres. -/
def TorusCentralizerParameterSmoothnessStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (G : GroupScheme S) [Smooth G.X.hom],
    (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (f : Spec (CommRingCat.of A) ⟶ S), IsAffineHom ((baseChange f).obj G).X.hom) →
    ∀ (M : Over S) [LocallyOfFiniteType M.hom] (H : GroupScheme M.left) [Smooth H.X.hom]
      (c : H ⟶ (baseChange M.hom).obj G),
      IsClosedSubgroup c → HasTorusCentralizerResidueFibres c →
      (∀ (U : Over S) (F : SubgroupFunctor ((baseChange U.hom).obj G)),
        IsAdmissible F → ∃! a : U ⟶ M, evaluate c a = F.centralizer) →
      Smooth M.hom

theorem smooth_of_torusCentralizerParameter : TorusCentralizerParameterSmoothnessStatement.{u} := by
  intro S _ G _ hA M _ H _ c hc hF hU
  apply Langlands.AlgebraicGeometry.ArtinianLiftingSmooth.smooth_of_liftsArtinian
  intro A B _ _ _ _ _ _ φ hφ he α β w _
  let I := RingHom.ker φ
  have hI : IsNilpotent I := by
    have hm : I ≤ maximalIdeal A := le_maximalIdeal (RingHom.ker_ne_top φ)
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot]
    apply le_antisymm _ bot_le
    calc
      I * I ≤ maximalIdeal A * I := Ideal.mul_mono_left hm
      _ = ⊥ := he
  let e : A ⧸ I ≃+* B := RingHom.quotientKerEquivOfSurjective hφ
  let eS := Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso e).op
  let q := Spec.algebraMap A (A ⧸ I)
  let r := Spec.map (CommRingCat.ofHom φ)
  have hqe : eS.hom ≫ q = r := by
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have : Nontrivial (A ⧸ I) := e.symm.injective.nontrivial
  have : IsLocalRing (A ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  have : IsArtinianRing (A ⧸ I) := e.symm.isArtinianRing
  have : Smooth ((baseChange β).obj G).X.hom :=
    MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  have : IsAffineHom ((baseChange β).obj G).X.hom := hA A β
  have : Smooth ((baseChange (Over.mk (q ≫ β)).hom).obj G).X.hom :=
    MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  have : IsAffineHom ((baseChange (Over.mk (q ≫ β)).hom).obj G).X.hom := hA (A ⧸ I) (q ≫ β)
  let a₀ : Over.mk (q ≫ β) ⟶ M := Over.homMk (eS.inv ≫ α) (by
    change (eS.inv ≫ α) ≫ M.hom = q ≫ β
    rw [Category.assoc, w]
    change eS.inv ≫ r ≫ β = q ≫ β
    rw [← hqe, Category.assoc, Iso.inv_hom_id_assoc])
  obtain ⟨a, ha⟩ := exists_lift_over_quotient c hc hF hU I β hI a₀
  have ha' : q ≫ a.left = eS.inv ≫ α := congrArg (fun m => m.left) ha
  refine ⟨a.left, a.w, ?_⟩
  change r ≫ a.left = α
  rw [← hqe, Category.assoc, ha', Iso.hom_inv_id_assoc]

end Langlands.GroupScheme.TorusSubgroupModuli
