import Langlands.GroupScheme.SchemeActionQuotientGeometry

/-! # Descent from local all-test families of orbit representatives -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
  Langlands.AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchemeAction

variable {S : Scheme.{u}} {A : GroupScheme S} {X : Over S}
  (b : SchemeAction A X) {U M : Over S} (π : M ⟶ U) (s : M ⟶ X)

/-- The orbit family, retaining the local base parameter. -/
def parameterSectionMap : A.X ⨯ M ⟶ X ⨯ U :=
  prod.lift (b.act prod.fst (prod.snd ≫ s)) (prod.snd ≫ π)

@[simp] theorem parameterSectionMap_apply {T : Over S}
    (d : T ⟶ A.X) (m : T ⟶ M) :
    prod.lift d m ≫ b.parameterSectionMap π s =
      prod.lift (b.act d (m ≫ s)) (m ≫ π) := by
  simp only [parameterSectionMap, prod.comp_lift, b.naturality,
    prod.lift_fst, prod.lift_snd_assoc]

variable (h : ∀ (T : Over S), Function.Bijective
  (fun z : (T ⟶ A.X) × (T ⟶ M) =>
    prod.lift (b.act z.1 (z.2 ≫ s)) (z.2 ≫ π)))

include h in
/-- A unique decomposition on all tests makes the orbit family an isomorphism. -/
theorem parameterSectionMap_isIso : IsIso (b.parameterSectionMap π s) := by
  refine isIso_of_yoneda_map_bijective _ fun T => ⟨?_, ?_⟩
  · intro f g hfg
    change f ≫ b.parameterSectionMap π s = g ≫ b.parameterSectionMap π s at hfg
    have hz : (f ≫ prod.fst, f ≫ prod.snd) =
        (g ≫ prod.fst, g ≫ prod.snd) := by
      apply (h T).1
      simpa only [parameterSectionMap, prod.comp_lift, b.naturality,
        Category.assoc] using hfg
    apply prod.hom_ext
    · exact congrArg Prod.fst hz
    · exact congrArg Prod.snd hz
  · intro p
    obtain ⟨⟨d, m⟩, hp⟩ := (h T).2 p
    exact ⟨prod.lift d m, (b.parameterSectionMap_apply π s d m).trans hp⟩

/-- The product presentation defined by a local family of representatives. -/
def parameterSectionIso : A.X ⨯ M ≅ X ⨯ U :=
  letI := b.parameterSectionMap_isIso π s h
  asIso (b.parameterSectionMap π s)

/-- The class morphism of the local family. -/
def parameterSectionClassMap : X ⨯ U ⟶ M :=
  (b.parameterSectionIso π s h).inv ≫ prod.snd

/-- The acting-group coordinate of a point in the local product presentation. -/
def parameterSectionGroupCoordinate {T : Over S} (p : T ⟶ X ⨯ U) : T ⟶ A.X :=
  p ≫ (b.parameterSectionIso π s h).inv ≫ prod.fst

theorem parameterSection_coordinates {T : Over S} (p : T ⟶ X ⨯ U) :
    prod.lift (b.parameterSectionGroupCoordinate π s h p)
      (p ≫ b.parameterSectionClassMap π s h) ≫
        (b.parameterSectionIso π s h).hom = p := by
  simp only [parameterSectionGroupCoordinate, parameterSectionClassMap,
    ← prod.comp_lift, prod.lift_fst_snd, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The class morphism retains the local base parameter. -/
theorem parameterSectionClassMap_comp :
    b.parameterSectionClassMap π s h ≫ π = prod.snd := by
  apply (cancel_epi (b.parameterSectionIso π s h).hom).mp
  simp only [parameterSectionClassMap, Category.assoc, Iso.hom_inv_id_assoc]
  change prod.snd ≫ π = b.parameterSectionMap π s ≫ prod.snd
  simp only [parameterSectionMap, prod.lift_snd]

/-- In these product coordinates the action multiplies the group coordinate. -/
theorem parameterSection_action {T : Over S} (d : T ⟶ A.X)
    (p : T ⟶ X ⨯ U) :
    prod.lift (b.act d (p ≫ prod.fst)) (p ≫ prod.snd) =
      prod.lift (d * b.parameterSectionGroupCoordinate π s h p)
        (p ≫ b.parameterSectionClassMap π s h) ≫
          (b.parameterSectionIso π s h).hom := by
  conv_lhs => rw [← b.parameterSection_coordinates π s h p]
  change prod.lift
      (b.act d ((prod.lift _ _ ≫ b.parameterSectionMap π s) ≫ prod.fst))
      ((prod.lift _ _ ≫ b.parameterSectionMap π s) ≫ prod.snd) =
    prod.lift _ _ ≫ b.parameterSectionMap π s
  rw [b.parameterSectionMap_apply, b.parameterSectionMap_apply]
  simp only [prod.lift_fst, prod.lift_snd, b.act_mul]

/-- The class morphism is invariant under the action on its first factor. -/
theorem parameterSectionClassMap_invariant {T : Over S}
    (d : T ⟶ A.X) (p : T ⟶ X ⨯ U) :
    prod.lift (b.act d (p ≫ prod.fst)) (p ≫ prod.snd) ≫
        b.parameterSectionClassMap π s h =
      p ≫ b.parameterSectionClassMap π s h := by
  rw [b.parameterSection_action π s h]
  simp only [parameterSectionClassMap, Category.assoc,
    Iso.hom_inv_id_assoc, prod.lift_snd]

/-- The exact action kernel of the local class morphism, on the original test. -/
theorem parameterSectionClassMap_eq_iff {T : Over S} (p p' : T ⟶ X ⨯ U) :
    p ≫ b.parameterSectionClassMap π s h =
        p' ≫ b.parameterSectionClassMap π s h ↔
      p ≫ prod.snd = p' ≫ prod.snd ∧
        ∃ d : T ⟶ A.X, b.act d (p ≫ prod.fst) = p' ≫ prod.fst := by
  constructor
  · intro hp
    have hbase := congrArg (fun f => f ≫ π) hp
    rw [Category.assoc, Category.assoc,
      b.parameterSectionClassMap_comp π s h] at hbase
    refine ⟨hbase, b.parameterSectionGroupCoordinate π s h p' *
      (b.parameterSectionGroupCoordinate π s h p)⁻¹, ?_⟩
    have he :
        prod.lift
            (b.act (b.parameterSectionGroupCoordinate π s h p' *
              (b.parameterSectionGroupCoordinate π s h p)⁻¹) (p ≫ prod.fst))
            (p ≫ prod.snd) = p' := by
      rw [b.parameterSection_action π s h, inv_mul_cancel_right, hp,
        b.parameterSection_coordinates π s h]
    simpa only [prod.lift_fst] using congrArg (fun f => f ≫ prod.fst) he
  · rintro ⟨hbase, d, hd⟩
    have he : prod.lift (b.act d (p ≫ prod.fst)) (p ≫ prod.snd) = p' := by
      apply prod.hom_ext
      · simpa only [prod.lift_fst] using hd
      · simpa only [prod.lift_snd] using hbase
    rw [← he, b.parameterSectionClassMap_invariant π s h]

/-- The local class morphism is flat when the acting group is flat. -/
theorem parameterSectionClassMap_flat [Flat A.X.hom] :
    Flat (b.parameterSectionClassMap π s h).left := by
  have : IsIso (b.parameterSectionIso π s h).inv.left :=
    (Over.forget S).map_isIso _
  have : Flat (prod.snd : A.X ⨯ M ⟶ M).left := by
    exact MorphismProperty.of_isPullback (P := @Flat.{u})
      (Over.isPullback_of_binaryFan_isLimit
        (BinaryFan.mk (prod.fst : A.X ⨯ M ⟶ A.X) prod.snd) (prodIsProd A.X M))
      inferInstance
  change Flat ((b.parameterSectionIso π s h).inv.left ≫
    (prod.snd : A.X ⨯ M ⟶ M).left)
  infer_instance

/-- The local class morphism is locally finitely presented when the group is. -/
theorem parameterSectionClassMap_locallyOfFinitePresentation
    [LocallyOfFinitePresentation A.X.hom] :
    LocallyOfFinitePresentation (b.parameterSectionClassMap π s h).left := by
  have : IsIso (b.parameterSectionIso π s h).inv.left :=
    (Over.forget S).map_isIso _
  have : LocallyOfFinitePresentation (prod.snd : A.X ⨯ M ⟶ M).left := by
    exact MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation.{u})
      (Over.isPullback_of_binaryFan_isLimit
        (BinaryFan.mk (prod.fst : A.X ⨯ M ⟶ A.X) prod.snd) (prodIsProd A.X M))
      inferInstance
  change LocallyOfFinitePresentation ((b.parameterSectionIso π s h).inv.left ≫
    (prod.snd : A.X ⨯ M ⟶ M).left)
  infer_instance

/-- The identity of the group gives surjectivity of the local class morphism. -/
theorem parameterSectionClassMap_surjective :
    Surjective (b.parameterSectionClassMap π s h).left := by
  have : IsIso (b.parameterSectionIso π s h).inv.left :=
    (Over.forget S).map_isIso _
  let r : M ⟶ A.X ⨯ M := prod.lift (1 : M ⟶ A.X) (𝟙 M)
  have hr : r.left ≫ (prod.snd : A.X ⨯ M ⟶ M).left = 𝟙 M.left :=
    congrArg (fun f => f.left) (prod.lift_snd (1 : M ⟶ A.X) (𝟙 M))
  have hr' : Surjective (r.left ≫ (prod.snd : A.X ⨯ M ⟶ M).left) := by
    rw [hr]
    infer_instance
  have := Surjective.of_comp r.left (prod.snd : A.X ⨯ M ⟶ M).left
  change Surjective ((b.parameterSectionIso π s h).inv.left ≫
    (prod.snd : A.X ⨯ M ⟶ M).left)
  infer_instance

/-- Local separated, locally quasi-finite families of orbit representatives
descend to a representation of the canonical action quotient. -/
def quotientRepresentationOfLocalSections
    (hfree : ∀ (T : Over S) (p : T ⟶ X),
      Function.Injective (fun d : T ⟶ A.X => b.act d p))
    [Flat A.X.hom] [LocallyOfFinitePresentation A.X.hom]
    (J : Sieve (Over.mk (𝟙 S))) (hJ : J ∈ fppfTopology S (Over.mk (𝟙 S)))
    (hlocal : ∀ ⦃U : Over S⦄ (g : U ⟶ Over.mk (𝟙 S)), J g →
      ∃ (M : Over S) (π : M ⟶ U) (s : M ⟶ X),
        IsSeparated π.left ∧ LocallyQuasiFinite π.left ∧
        LocallyOfFiniteType π.left ∧
        ∀ (T : Over S), Function.Bijective
          (fun z : (T ⟶ A.X) × (T ⟶ M) =>
            prod.lift (b.act z.1 (z.2 ≫ s)) (z.2 ≫ π))) :
    b.QuotientRepresentation := by
  apply b.quotientRepresentationOfLocalPresentations hfree J hJ
  intro U g hg
  obtain ⟨M, π, s, hsep, hlqf, hlft, h⟩ := hlocal g hg
  exact ⟨M, π, b.parameterSectionClassMap π s h,
    b.parameterSectionClassMap_flat π s h,
    b.parameterSectionClassMap_locallyOfFinitePresentation π s h,
    b.parameterSectionClassMap_surjective π s h,
    b.parameterSectionClassMap_comp π s h, hsep, hlqf, hlft,
    fun _ p p' => b.parameterSectionClassMap_eq_iff π s h p p'⟩

end Langlands.GroupScheme.SchemeAction

namespace Langlands.GroupScheme.GroupIsomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  (I : GroupIsomorphismScheme G H) (a : AutomorphicAction A G)

/-- Local geometric families with unique adjoint decomposition give an actual
outer quotient by effective descent of the canonical quotient sheaf. -/
def outerOfLocalSections (ha : a.IsFaithful)
    [Flat A.X.hom] [LocallyOfFinitePresentation A.X.hom] [QuasiCompact A.X.hom]
    (J : Sieve (Over.mk (𝟙 S))) (hJ : J ∈ fppfTopology S (Over.mk (𝟙 S)))
    (hlocal : ∀ ⦃U : Over S⦄ (g : U ⟶ Over.mk (𝟙 S)), J g →
      ∃ (M : Over S) (π : M ⟶ U) (s : M ⟶ I.parameter),
        IsSeparated π.left ∧ LocallyQuasiFinite π.left ∧
        LocallyOfFiniteType π.left ∧
        ∀ (T : Over S), Function.Bijective
          (fun z : (T ⟶ A.X) × (T ⟶ M) =>
            prod.lift (SchemeAction.act (I.modObj a) z.1 (z.2 ≫ s)) (z.2 ≫ π))) :
    OuterIsomorphismScheme I a :=
  I.outerOfQuotientRepresentation a ha
    (SchemeAction.quotientRepresentationOfLocalSections (I.modObj a)
      (I.actionHom_injective_of_isFaithful a ha) J hJ hlocal)

end Langlands.GroupScheme.GroupIsomorphismScheme
