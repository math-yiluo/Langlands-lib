/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Etale.StandardEtale
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

/-!
# The strict henselization is a strictly henselian local ring

Let `s : Spec Ω ⟶ S` be a geometric point of a scheme `S`. The strict henselization
`𝒪^{sh}_{S,s}`, the colimit of the rings of the affine pointed étale neighbourhoods of `s`, is
a henselian local ring with separably closed residue field, and the geometric point `s` factors
through the closed point of the strict localization `S_(s) = Spec 𝒪^{sh}_{S,s}`.

The proof goes through the evaluation map `strictHenselizationEval s : 𝒪^{sh}_{S,s} ⟶ Ω`. The
key point is `exists_isRoot_and_strictHenselizationEval_eq`: a monic polynomial over the
colimit whose image over `Ω` has a simple root `β` has a root with value `β`. Indeed, the
polynomial descends to some neighbourhood `Spec R`, and the standard étale algebra
`(R[X]/f)[1/f']` is a further neighbourhood carrying an honest root. The same argument with
the standard étale algebra `R[X]/(X - c)[1/X] = R[1/c]` shows that the elements with nonzero
value are units, so the strict henselization is local with maximal ideal the kernel of the
evaluation.

## References

- Stacks Project, Lemma 59.33.1, <https://stacks.math.columbia.edu/tag/04HX>
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Polynomial

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

instance : PreservesColimitsOfShape (AffinePointedEtaleNeighborhood s)ᵒᵖ
    (CategoryTheory.forget CommRingCat.{u}) :=
  FinallySmall.preservesColimitsOfShape_of_isFiltered.{u} _ _

set_option backward.isDefEq.respectTransparency false in
/-- The evaluation of germs at the geometric point: the ring homomorphism
`𝒪^{sh}_{S,s} ⟶ Ω` induced by the maps `Γ(V, 𝒪_V) ⟶ Γ(Spec Ω, 𝒪) ≅ Ω` given by the lifts
`v : Spec Ω ⟶ V` of `s`. -/
noncomputable def strictHenselizationEval : strictHenselization s ⟶ CommRingCat.of Ω :=
  colimit.desc (strictHenselizationDiagram s)
    { pt := CommRingCat.of Ω
      ι :=
        { app x := Scheme.Γ.map (x.unop.obj.2.left).op ≫ (Scheme.ΓSpecIso (.of Ω)).hom
          naturality x y f := by
            have h : y.unop.obj.2.left ≫ f.unop.hom.1.left = x.unop.obj.2.left :=
              congrArg CommaMorphism.left f.unop.hom.2
            change Scheme.Γ.map f.unop.hom.1.left.op ≫ Scheme.Γ.map y.unop.obj.2.left.op ≫ _ =
              (Scheme.Γ.map x.unop.obj.2.left.op ≫ _) ≫ 𝟙 _
            rw [Category.comp_id, ← h, op_comp, Scheme.Γ.map_comp, Category.assoc] } }

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ι_strictHenselizationEval (x : AffinePointedEtaleNeighborhood s) :
    colimit.ι (strictHenselizationDiagram s) (op x) ≫ strictHenselizationEval s =
      Scheme.Γ.map (x.obj.2.left).op ≫ (Scheme.ΓSpecIso (.of Ω)).hom :=
  colimit.ι_desc _ _

/-- A pointed étale neighbourhood of `s` given by a ring: an étale morphism `Spec R ⟶ S`
together with a ring homomorphism `R ⟶ Ω` such that `Spec Ω ⟶ Spec R ⟶ S` is `s`. -/
structure SpecPointedEtaleNeighborhood where
  /-- the ring of the neighbourhood -/
  R : CommRingCat.{u}
  /-- the structure morphism of the neighbourhood -/
  hom : Spec R ⟶ S
  etale : Etale hom
  /-- the lift of the geometric point, as a ring homomorphism -/
  pt : R ⟶ CommRingCat.of Ω
  w : Spec.map pt ≫ hom = s

namespace SpecPointedEtaleNeighborhood

attribute [instance] SpecPointedEtaleNeighborhood.etale

variable {s} (N : SpecPointedEtaleNeighborhood s)

set_option backward.isDefEq.respectTransparency.types false in
/-- The affine pointed étale neighbourhood `(Spec R, Spec.map pt)` of `s`. -/
noncomputable def toAffine : AffinePointedEtaleNeighborhood s :=
  ⟨Functor.elementsMk _ (Etale.mk N.hom) (CategoryTheory.Over.homMk (Spec.map N.pt) N.w),
    (inferInstance : IsAffine (Spec N.R))⟩

set_option backward.isDefEq.respectTransparency.types false in
lemma toAffine_left : N.toAffine.obj.2.left = Spec.map N.pt := rfl

/-- The canonical map from the ring of a pointed étale neighbourhood `Spec R` of `s` to the
strict henselization. -/
noncomputable def ι : N.R ⟶ strictHenselization s :=
  (Scheme.ΓSpecIso N.R).inv ≫ colimit.ι (strictHenselizationDiagram s) (op N.toAffine)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ι_comp_strictHenselizationEval : N.ι ≫ strictHenselizationEval s = N.pt := by
  rw [ι, Category.assoc, ι_strictHenselizationEval, toAffine_left,
    Scheme.Γ_map_op, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

@[simp]
lemma strictHenselizationEval_ι (c : N.R) :
    strictHenselizationEval s (N.ι c) = N.pt c := by
  rw [← CommRingCat.comp_apply, N.ι_comp_strictHenselizationEval]

set_option backward.isDefEq.respectTransparency false in
lemma comp_ι {N N' : SpecPointedEtaleNeighborhood s} (u : N.R ⟶ N'.R)
    (hu : Spec.map u ≫ N.hom = N'.hom) (hu' : u ≫ N'.pt = N.pt) :
    u ≫ N'.ι = N.ι := by
  let g : (Etale.mk N'.hom : S.Etale) ⟶ Etale.mk N.hom :=
    MorphismProperty.Over.homMk (Spec.map u) hu
  have hg : (pointSmallEtale s).fiber.map g N'.toAffine.obj.2 = N.toAffine.obj.2 := by
    apply CategoryTheory.Over.OverMorphism.ext
    change Spec.map N'.pt ≫ Spec.map u = Spec.map N.pt
    rw [← Spec.map_comp, hu']
  let f : N'.toAffine ⟶ N.toAffine := ObjectProperty.homMk (Functor.Elements.homMk g hg)
  have h2 : Scheme.Γ.map (Spec.map u).op ≫
      colimit.ι (strictHenselizationDiagram s) (op N'.toAffine) =
      colimit.ι (strictHenselizationDiagram s) (op N.toAffine) :=
    colimit.w (strictHenselizationDiagram s) f.op
  rw [ι, ι, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    ← Scheme.Γ_map_op, h2]

end SpecPointedEtaleNeighborhood

section Descent

variable {s}

lemma range_colimit_ι_subset {x y : AffinePointedEtaleNeighborhood s} (f : x ⟶ y) :
    Set.range (colimit.ι (strictHenselizationDiagram s) (op y)) ⊆
      Set.range (colimit.ι (strictHenselizationDiagram s) (op x)) := by
  rintro _ ⟨b, rfl⟩
  exact ⟨(strictHenselizationDiagram s).map f.op b,
    by rw [← CommRingCat.comp_apply, colimit.w]⟩

/-- Any finite family of elements of the strict henselization comes from a single affine
pointed étale neighbourhood. -/
lemma exists_forall_mem_range_colimit_ι (n : ℕ) (a : Fin n → ToType (strictHenselization s)) :
    ∃ x : AffinePointedEtaleNeighborhood s,
      ∀ i, a i ∈ Set.range (colimit.ι (strictHenselizationDiagram s) (op x)) := by
  induction n with
  | zero =>
    obtain ⟨x⟩ := IsCofiltered.nonempty (C := AffinePointedEtaleNeighborhood s)
    exact ⟨x, fun i ↦ i.elim0⟩
  | succ n ih =>
    obtain ⟨x, hx⟩ := ih (fun i ↦ a i.succ)
    obtain ⟨y, z, hz⟩ := Concrete.colimit_exists_rep (strictHenselizationDiagram s) (a 0)
    refine ⟨IsCofiltered.min x y.unop, Fin.cases ?_ ?_⟩
    · exact range_colimit_ι_subset (IsCofiltered.minToRight _ _) ⟨z, hz⟩
    · exact fun i ↦ range_colimit_ι_subset (IsCofiltered.minToLeft _ _) (hx i)

set_option backward.isDefEq.respectTransparency false in
lemma SpecPointedEtaleNeighborhood.colimit_ι_mem_range_ι (N : SpecPointedEtaleNeighborhood s)
    (b : Γ(Spec N.R, ⊤)) :
    colimit.ι (strictHenselizationDiagram s) (op N.toAffine) b ∈ Set.range N.ι := by
  refine ⟨(Scheme.ΓSpecIso N.R).hom b, ?_⟩
  have h : (Scheme.ΓSpecIso N.R).hom ≫ N.ι =
      colimit.ι (strictHenselizationDiagram s) (op N.toAffine) := by
    rw [SpecPointedEtaleNeighborhood.ι, Iso.hom_inv_id_assoc]
  exact congr($h b)

set_option backward.isDefEq.respectTransparency false in
/-- Every affine pointed étale neighbourhood of `s` is refined by one of the form `Spec R`. -/
lemma exists_specPointedEtaleNeighborhood_range_subset (x : AffinePointedEtaleNeighborhood s) :
    ∃ N : SpecPointedEtaleNeighborhood s,
      Set.range (colimit.ι (strictHenselizationDiagram s) (op x)) ⊆ Set.range N.ι := by
  let y : Spec (CommRingCat.of Ω) ⟶ x.obj.1.left := x.obj.2.left
  have hyw : y ≫ x.obj.1.hom = s := CategoryTheory.Over.w x.obj.2
  obtain ⟨R, j, hj, hmem, -⟩ := exists_affine_mem_range_and_range_subset
    (x := y default) (U := ⊤) trivial
  have hsub : Set.range y ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z default]
  have hl : IsOpenImmersion.lift j y hsub ≫ j = y := IsOpenImmersion.lift_fac _ _ _
  have hspec : Spec.map (Spec.preimage (IsOpenImmersion.lift j y hsub)) =
    IsOpenImmersion.lift j y hsub := Spec.map_preimage _
  have hw : Spec.map (Spec.preimage (IsOpenImmersion.lift j y hsub)) ≫
      (j ≫ x.obj.1.hom) = s := by
    rw [hspec, ← Category.assoc, hl, hyw]
  let N : SpecPointedEtaleNeighborhood s :=
    ⟨R, j ≫ x.obj.1.hom, inferInstance, Spec.preimage (IsOpenImmersion.lift j y hsub), hw⟩
  let g : (Etale.mk N.hom : S.Etale) ⟶ x.obj.1 := MorphismProperty.Over.homMk j rfl
  have hg : (pointSmallEtale s).fiber.map g N.toAffine.obj.2 = x.obj.2 := by
    apply CategoryTheory.Over.OverMorphism.ext
    change Spec.map (Spec.preimage (IsOpenImmersion.lift j y hsub)) ≫ j = y
    rw [hspec, hl]
  refine ⟨N, subset_trans (range_colimit_ι_subset
    (ObjectProperty.homMk (Functor.Elements.homMk g hg) : N.toAffine ⟶ x)) ?_⟩
  rintro _ ⟨b, rfl⟩
  exact N.colimit_ι_mem_range_ι b

/-- Any finite family of elements of the strict henselization comes from a single pointed
étale neighbourhood of the form `Spec R`. -/
lemma exists_specPointedEtaleNeighborhood_forall_mem_range (n : ℕ)
    (a : Fin n → ToType (strictHenselization s)) :
    ∃ N : SpecPointedEtaleNeighborhood s, ∀ i, a i ∈ Set.range N.ι := by
  obtain ⟨x, hx⟩ := exists_forall_mem_range_colimit_ι n a
  obtain ⟨N, hN⟩ := exists_specPointedEtaleNeighborhood_range_subset x
  exact ⟨N, fun i ↦ hN (hx i)⟩

end Descent

section StandardEtale

variable {s}

set_option backward.isDefEq.respectTransparency false in
/-- Given a pointed étale neighbourhood `Spec R` of `s`, a standard étale pair `P` over `R`
and a point `β : Ω` at which `P.f` vanishes and `P.g` is invertible, the standard étale algebra
of `P` is again a pointed étale neighbourhood of `s`, and it carries a root of `P.f`. -/
lemma SpecPointedEtaleNeighborhood.exists_standardEtale (N : SpecPointedEtaleNeighborhood s)
    (P : StandardEtalePair ↑N.R) (β : Ω)
    (h₁ : (P.f.map N.pt.hom).eval β = 0) (h₂ : (P.g.map N.pt.hom).eval β ≠ 0) :
    ∃ (N' : SpecPointedEtaleNeighborhood s) (u : N.R ⟶ N'.R) (t : N'.R),
      u ≫ N'.ι = N.ι ∧ (P.f.map u.hom).eval t = 0 ∧
        IsUnit ((P.g.map u.hom).eval t) ∧ N'.pt t = β := by
  let _inst : Algebra ↑N.R Ω := N.pt.hom.toAlgebra
  have halg : algebraMap ↑N.R Ω = N.pt.hom := N.pt.hom.algebraMap_toAlgebra
  have hae : ∀ (p : (↑N.R)[X]) (x : Ω), aeval x p = (p.map N.pt.hom).eval x := fun p x ↦ by
    rw [Polynomial.eval_map, Polynomial.aeval_def, halg]
  have hβ : P.HasMap β :=
    ⟨by rw [hae]; exact h₁, by rw [hae]; exact isUnit_iff_ne_zero.mpr h₂⟩
  have hae' : ∀ (p : (↑N.R)[X]) (x : P.Ring),
      aeval x p = (p.map (CommRingCat.ofHom (algebraMap ↑N.R P.Ring)).hom).eval x :=
    fun p x ↦ by
    rw [Polynomial.eval_map, Polynomial.aeval_def, CommRingCat.hom_ofHom]
  have hetale : Etale (Spec.map (CommRingCat.ofHom (algebraMap ↑N.R P.Ring))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (by rw [CommRingCat.hom_ofHom]; exact RingHom.etale_algebraMap.mpr inferInstance)
  have hpt : CommRingCat.ofHom (algebraMap ↑N.R P.Ring) ≫
      CommRingCat.ofHom (P.lift β hβ).toRingHom = N.pt := by
    ext r
    change (P.lift β hβ) (algebraMap ↑N.R P.Ring r) = N.pt r
    rw [AlgHom.commutes, halg]
  refine ⟨⟨CommRingCat.of P.Ring,
      Spec.map (CommRingCat.ofHom (algebraMap ↑N.R P.Ring)) ≫ N.hom, inferInstance,
      CommRingCat.ofHom (P.lift β hβ).toRingHom, ?_⟩,
    CommRingCat.ofHom (algebraMap ↑N.R P.Ring), P.X, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, hpt, N.w]
  · exact comp_ι _ rfl hpt
  · rw [← hae']; exact P.hasMap_X.1
  · rw [← hae']; exact P.hasMap_X.2
  · exact P.lift_X β hβ

end StandardEtale

section Local

variable {s}

/-- An element of the strict henselization with nonzero value at the geometric point is a
unit. -/
lemma isUnit_of_strictHenselizationEval_ne_zero {a : ↑(strictHenselization s)}
    (ha : strictHenselizationEval s a ≠ 0) : IsUnit a := by
  obtain ⟨N, hN⟩ := exists_specPointedEtaleNeighborhood_forall_mem_range 1 (fun _ ↦ a)
  obtain ⟨c, rfl⟩ := hN 0
  rw [SpecPointedEtaleNeighborhood.strictHenselizationEval_ι] at ha
  obtain ⟨N', u, t, hu, ht, htu, -⟩ := N.exists_standardEtale
    ⟨X - C c, monic_X_sub_C c, X, X, 0, 1, by simp⟩ (N.pt c) (by simp) (by simpa using ha)
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, eval_sub, eval_X,
    eval_C, sub_eq_zero] at ht
  rw [Polynomial.map_X, eval_X, ht] at htu
  rw [← hu, CommRingCat.comp_apply]
  exact htu.map N'.ι.hom

/-- An element of the strict henselization is a unit iff its value at the geometric point is
nonzero. -/
lemma isUnit_iff_strictHenselizationEval_ne_zero (a : ↑(strictHenselization s)) :
    IsUnit a ↔ strictHenselizationEval s a ≠ 0 :=
  ⟨fun h ↦ (h.map (strictHenselizationEval s).hom).ne_zero,
    isUnit_of_strictHenselizationEval_ne_zero⟩

/-- The strict henselization is a nontrivial ring. -/
instance nontrivial_strictHenselization : Nontrivial ↑(strictHenselization s) :=
  ⟨1, 0, fun h ↦ one_ne_zero (α := Ω)
    (by rw [← map_one (strictHenselizationEval s).hom, h, map_zero])⟩

variable (s) in
/-- The strict henselization is a local ring. -/
instance isLocalRing_strictHenselization : IsLocalRing (strictHenselization s) :=
  .of_nonunits_add fun a b ha hb ↦ by
    simp only [mem_nonunits_iff, isUnit_iff_strictHenselizationEval_ne_zero, not_not] at ha hb ⊢
    rw [map_add, ha, hb, add_zero]

/-- An element of the strict henselization lies in the maximal ideal iff its value at the
geometric point vanishes. -/
lemma mem_maximalIdeal_strictHenselization_iff (a : ↑(strictHenselization s)) :
    a ∈ IsLocalRing.maximalIdeal ↑(strictHenselization s) ↔
      strictHenselizationEval s a = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_iff_strictHenselizationEval_ne_zero, not_not]

/-- The maximal ideal of the strict henselization is the kernel of the evaluation at the
geometric point. -/
lemma maximalIdeal_strictHenselization :
    IsLocalRing.maximalIdeal ↑(strictHenselization s) =
      RingHom.ker (strictHenselizationEval s).hom :=
  Ideal.ext fun a ↦ (mem_maximalIdeal_strictHenselization_iff a).trans RingHom.mem_ker.symm

end Local

section Henselian

variable {s}

/-- The key lemma: a monic polynomial over the strict henselization whose reduction at the
geometric point has a simple root `β` already has a root in the strict henselization, with
value `β` at the geometric point. -/
lemma exists_isRoot_and_strictHenselizationEval_eq
    {f : (↑(strictHenselization s))[X]} (hf : f.Monic) {β : Ω}
    (h₁ : (f.map (strictHenselizationEval s).hom).eval β = 0)
    (h₂ : (derivative (f.map (strictHenselizationEval s).hom)).eval β ≠ 0) :
    ∃ a : ↑(strictHenselization s), f.IsRoot a ∧ strictHenselizationEval s a = β := by
  obtain ⟨N, hN⟩ :=
    exists_specPointedEtaleNeighborhood_forall_mem_range (f.natDegree + 1) (fun i ↦ f.coeff i)
  have hlifts : f ∈ Polynomial.lifts N.ι.hom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ≤ f.natDegree
    · exact hN ⟨n, by omega⟩
    · rw [f.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact ⟨0, map_zero _⟩
  obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hf
  have hcomp : (strictHenselizationEval s).hom.comp N.ι.hom = N.pt.hom := by
    rw [← CommRingCat.hom_comp, N.ι_comp_strictHenselizationEval]
  have hmap : f.map (strictHenselizationEval s).hom = g.map N.pt.hom := by
    rw [← hg, Polynomial.map_map, hcomp]
  obtain ⟨N', u, t, hu, ht, -, hpt⟩ := N.exists_standardEtale
    ⟨g, hgm, derivative g, 1, 0, 1, by simp⟩ β (by rwa [← hmap]) (by
      rw [← Polynomial.derivative_map, ← hmap]; exact h₂)
  refine ⟨N'.ι t, ?_, by rw [SpecPointedEtaleNeighborhood.strictHenselizationEval_ι, hpt]⟩
  have : f = (g.map u.hom).map N'.ι.hom := by
    rw [Polynomial.map_map, ← CommRingCat.hom_comp, hu, hg]
  rw [Polynomial.IsRoot.def, this, Polynomial.eval_map_apply, ht, map_zero]

variable (s) in
/-- The strict henselization is a henselian local ring. -/
instance henselianLocalRing_strictHenselization :
    HenselianLocalRing (strictHenselization s) where
  is_henselian f hf a₀ h₁ h₂ := by
    rw [mem_maximalIdeal_strictHenselization_iff] at h₁
    have e₁ : (f.map (strictHenselizationEval s).hom).eval
        (strictHenselizationEval s a₀) = 0 := by
      rw [Polynomial.eval_map_apply, h₁]
    have e₂ : (derivative (f.map (strictHenselizationEval s).hom)).eval
        (strictHenselizationEval s a₀) ≠ 0 := by
      rw [Polynomial.derivative_map, Polynomial.eval_map_apply]
      exact (h₂.map (strictHenselizationEval s).hom).ne_zero
    obtain ⟨a, ha, hb⟩ := exists_isRoot_and_strictHenselizationEval_eq hf e₁ e₂
    exact ⟨a, ha, by rw [mem_maximalIdeal_strictHenselization_iff, map_sub, hb, sub_self]⟩

variable (s) in
/-- The embedding of the residue field of the strict henselization into `Ω` induced by the
evaluation at the geometric point. -/
noncomputable def strictHenselizationResidueFieldEmb :
    IsLocalRing.ResidueField ↑(strictHenselization s) →+* Ω :=
  Ideal.Quotient.lift _ (strictHenselizationEval s).hom fun a ha ↦
    (mem_maximalIdeal_strictHenselization_iff a).1 ha

@[simp]
lemma strictHenselizationResidueFieldEmb_residue (a : ↑(strictHenselization s)) :
    strictHenselizationResidueFieldEmb s (IsLocalRing.residue _ a) =
      strictHenselizationEval s a :=
  rfl

lemma strictHenselizationResidueFieldEmb_comp_residue :
    (strictHenselizationResidueFieldEmb s).comp
      (IsLocalRing.residue ↑(strictHenselization s)) = (strictHenselizationEval s).hom :=
  RingHom.ext fun a ↦ strictHenselizationResidueFieldEmb_residue a

variable (s) in
/-- The residue field of the strict henselization is separably closed. -/
instance isSepClosed_residueField_strictHenselization :
    IsSepClosed (IsLocalRing.ResidueField (strictHenselization s)) := by
  refine IsSepClosed.of_exists_root _ fun p hpm hpi hps ↦ ?_
  obtain ⟨f, hf, -, hfm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective IsLocalRing.residue_surjective p) hpm
  have hmap : f.map (strictHenselizationEval s).hom =
      p.map (strictHenselizationResidueFieldEmb s) := by
    rw [← hf, Polynomial.map_map, strictHenselizationResidueFieldEmb_comp_residue]
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_root (k := Ω)
    (p.map (strictHenselizationResidueFieldEmb s))
    (by rw [hpm.degree_map]; exact (degree_pos_of_irreducible hpi).ne') hps.map
  have e₁ : (f.map (strictHenselizationEval s).hom).eval β = 0 := by rw [hmap]; exact hβ
  have e₂ : (derivative (f.map (strictHenselizationEval s).hom)).eval β ≠ 0 := by
    rw [hmap, Polynomial.derivative_map, Polynomial.eval_map]
    exact hps.eval₂_derivative_ne_zero _
      (by rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at hβ)
  obtain ⟨a, ha, -⟩ := exists_isRoot_and_strictHenselizationEval_eq hfm e₁ e₂
  exact ⟨IsLocalRing.residue _ a,
    by rw [← hf, Polynomial.eval_map_apply, ha.eq_zero, map_zero]⟩

end Henselian

set_option backward.isDefEq.respectTransparency false in
/-- The lift `v : Spec Ω ⟶ V` of the geometric point to an affine pointed étale neighbourhood
`(V, v)` is the composite of `Spec` of the evaluation map `𝒪^{sh}_{S,s} ⟶ Ω` with the leg
`S_(s) ⟶ V` of the limit cone. -/
@[reassoc]
lemma spec_map_strictHenselizationEval_comp_strictLocalizationCone_π_app
    (x : AffinePointedEtaleNeighborhood s) :
    Spec.map (strictHenselizationEval s) ≫ (strictLocalizationCone s).π.app x =
      x.obj.2.left := by
  let y : Spec (CommRingCat.of Ω) ⟶ x.obj.1.left := x.obj.2.left
  have hy : Spec.map (Scheme.Γ.map y.op ≫ (Scheme.ΓSpecIso (.of Ω)).hom) =
      y ≫ x.obj.1.left.toSpecΓ := by
    rw [Spec.map_comp, SpecMap_ΓSpecIso_hom, Scheme.Γ_map_op, Scheme.toSpecΓ_naturality]
  rw [strictLocalizationCone_π_app]
  change Spec.map (strictHenselizationEval s) ≫
    Spec.map (colimit.ι (strictHenselizationDiagram s) (op x)) ≫
      inv x.obj.1.left.toSpecΓ = y
  rw [← Spec.map_comp_assoc, ι_strictHenselizationEval]
  change Spec.map (Scheme.Γ.map y.op ≫ (Scheme.ΓSpecIso (.of Ω)).hom) ≫
    inv x.obj.1.left.toSpecΓ = y
  rw [hy, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The geometric point `s` is the composite of `Spec` of the evaluation map
`𝒪^{sh}_{S,s} ⟶ Ω` with the structure morphism `S_(s) ⟶ S`. -/
lemma spec_map_strictHenselizationEval_comp_strictLocalizationToBase :
    Spec.map (strictHenselizationEval s) ≫ strictLocalizationToBase s = s := by
  obtain ⟨x⟩ := IsCofiltered.nonempty (C := AffinePointedEtaleNeighborhood s)
  let y : Spec (CommRingCat.of Ω) ⟶ x.obj.1.left := x.obj.2.left
  have hyw : y ≫ x.obj.1.hom = s := CategoryTheory.Over.w x.obj.2
  have hy : Spec.map (Scheme.Γ.map y.op ≫ (Scheme.ΓSpecIso (.of Ω)).hom) =
      y ≫ x.obj.1.left.toSpecΓ := by
    rw [Spec.map_comp, SpecMap_ΓSpecIso_hom, Scheme.Γ_map_op, Scheme.toSpecΓ_naturality]
  rw [← strictLocalizationCone_π_app_hom s x, strictLocalizationCone_π_app]
  change (Spec.map (strictHenselizationEval s) ≫
    Spec.map (colimit.ι (strictHenselizationDiagram s) (op x)) ≫
      inv x.obj.1.left.toSpecΓ) ≫ x.obj.1.hom = s
  rw [← Spec.map_comp_assoc, ι_strictHenselizationEval]
  change (Spec.map (Scheme.Γ.map y.op ≫ (Scheme.ΓSpecIso (.of Ω)).hom) ≫
    inv x.obj.1.left.toSpecΓ) ≫ x.obj.1.hom = s
  rw [hy]
  have key : ∀ {A B C D : Scheme.{u}} (a : A ⟶ B) (t : B ⟶ C) [IsIso t] (h : B ⟶ D),
      (a ≫ t) ≫ inv t ≫ h = a ≫ h := by intros; simp
  exact (key _ _ _).trans hyw

/-- The geometric point `s` factors through the closed point of the strict localization: there
is an embedding `φ` of the residue field of `𝒪^{sh}_{S,s}` into `Ω` such that `s` is the
composite `Spec Ω ⟶ Spec κ ⟶ S_(s) ⟶ S`. -/
theorem exists_residueField_hom_strictLocalization :
    ∃ φ : IsLocalRing.ResidueField (strictHenselization s) →+* Ω,
      Spec.map (CommRingCat.ofHom (φ.comp (IsLocalRing.residue _))) ≫
        strictLocalizationToBase s = s := by
  refine ⟨strictHenselizationResidueFieldEmb s, ?_⟩
  rw [strictHenselizationResidueFieldEmb_comp_residue, CommRingCat.ofHom_hom]
  exact spec_map_strictHenselizationEval_comp_strictLocalizationToBase s


end AlgebraicGeometry.Scheme
