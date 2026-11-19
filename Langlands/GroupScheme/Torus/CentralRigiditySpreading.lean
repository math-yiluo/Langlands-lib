import Langlands.AlgebraicGeometry.SpecStalkFactorizationSpreadingStatement
import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Spreading equality of homomorphisms from `Spec 𝒪_{S,s}` to an open neighbourhood -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.CentralRigiditySpreading

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- The first projection intertwines a base-changed homomorphism with the original one. -/
theorem baseChange_map_left_fst {T : Scheme.{u}} (f : T ⟶ S) (w : H ⟶ G) :
    ((GroupScheme.baseChange f).map w).hom.hom.left ≫ pullback.fst G.X.hom f =
      pullback.fst H.X.hom f ≫ w.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- The second projection is preserved by a base-changed homomorphism. -/
theorem baseChange_map_left_snd {T : Scheme.{u}} (f : T ⟶ S) (w : H ⟶ G) :
    ((GroupScheme.baseChange f).map w).hom.hom.left ≫ pullback.snd G.X.hom f =
      pullback.snd H.X.hom f :=
  pullback.lift_snd _ _ _

/-- Two base-changed homomorphisms agree exactly when the underlying morphisms agree after
composing with the first projection of the pullback. -/
theorem baseChange_map_eq_iff {T : Scheme.{u}} (f : T ⟶ S) (u v : H ⟶ G) :
    (GroupScheme.baseChange f).map u = (GroupScheme.baseChange f).map v ↔
      pullback.fst H.X.hom f ≫ u.hom.hom.left = pullback.fst H.X.hom f ≫ v.hom.hom.left := by
  constructor
  · intro h
    rw [← baseChange_map_left_fst, ← baseChange_map_left_fst, h]
  · intro h
    ext1
    ext1
    apply pullback.hom_ext
    · exact (baseChange_map_left_fst f u).trans (h.trans (baseChange_map_left_fst f v).symm)
    · exact (baseChange_map_left_snd f u).trans (baseChange_map_left_snd f v).symm

/-- The kernel of the pair `(u, v)`: the pullback of the diagonal of `G` along `(u, v)`. -/
noncomputable abbrev eqLift (u v : H ⟶ G) : H.X.left ⟶ pullback G.X.hom G.X.hom :=
  pullback.lift u.hom.hom.left v.hom.hom.left (by simp)

/-- The inclusion of the kernel of the pair `(u, v)` into `H`. -/
noncomputable abbrev eqIncl (u v : H ⟶ G) :
    pullback (eqLift u v) (pullback.diagonal G.X.hom) ⟶ H.X.left :=
  pullback.fst _ _

/-- The kernel inclusion of a pair of homomorphisms is an immersion. -/
instance isImmersion_eqIncl (u v : H ⟶ G) : IsImmersion (eqIncl u v) := by
  dsimp only [eqIncl]
  infer_instance

/-- Over a locally noetherian source, the kernel inclusion is locally of finite
presentation. -/
theorem locallyOfFinitePresentation_eqIncl (u v : H ⟶ G) [IsLocallyNoetherian H.X.left] :
    LocallyOfFinitePresentation (eqIncl u v) :=
  LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance

/-- A morphism into `H` factors through the kernel of `(u, v)` exactly when `u` and `v`
agree on it. -/
theorem exists_factor_iff {T : Scheme.{u}} (u v : H ⟶ G) (t : T ⟶ H.X.left) :
    (∃ y, y ≫ eqIncl u v = t) ↔ t ≫ u.hom.hom.left = t ≫ v.hom.hom.left := by
  constructor
  · rintro ⟨y, rfl⟩
    have hc := pullback.condition (f := eqLift u v) (g := pullback.diagonal G.X.hom)
    have h1 := congrArg (· ≫ pullback.fst G.X.hom G.X.hom) hc
    have h2 := congrArg (· ≫ pullback.snd G.X.hom G.X.hom) hc
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
      pullback.diagonal_snd] at h1 h2
    simp only [Category.assoc, h1, h2]
  · intro h
    refine ⟨pullback.lift t (t ≫ u.hom.hom.left) ?_, pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      exact congrArg (t ≫ ·) (pullback.lift_fst _ _ _)
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
      exact (congrArg (t ≫ ·) (pullback.lift_snd _ _ _)).trans h.symm

/-- Equality over `Spec 𝒪_{S,s}` spreads to an open neighbourhood of `s`, given the
spreading statement for the kernel inclusion. -/
theorem exists_open_baseChange_eq
    (hP4 : Langlands.AlgebraicGeometry.SpecStalkFactorizationSpreadingStatement.{u})
    (u v : H ⟶ G) (s : S) (hqc : QuasiCompact H.X.hom) (hqs : QuasiSeparated H.X.hom)
    (hK : LocallyOfFinitePresentation (eqIncl u v))
    (h : (GroupScheme.baseChange (S.fromSpecStalk s)).map u =
      (GroupScheme.baseChange (S.fromSpecStalk s)).map v) :
    ∃ U : S.Opens, s ∈ U ∧
      (GroupScheme.baseChange U.ι).map u = (GroupScheme.baseChange U.ι).map v := by
  rw [baseChange_map_eq_iff] at h
  obtain ⟨U, hsU, hU⟩ := hP4 S H.X.left _ H.X.hom (eqIncl u v) s hqc hqs hK
    ((exists_factor_iff u v _).2 h)
  exact ⟨U, hsU, (baseChange_map_eq_iff _ u v).2 ((exists_factor_iff u v _).1 hU)⟩

end Langlands.GroupScheme.CentralRigiditySpreading
