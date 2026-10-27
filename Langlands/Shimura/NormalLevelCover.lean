import Langlands.Shimura.Levels
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! # Actual quotient actions on normal-level double quotients -/

noncomputable section

universe u v w

namespace Langlands.Shimura.LevelSpace

open CategoryTheory

variable {Γ : Type u} {G : Type v} {X : Type w}
variable [Group Γ] [Group G] [MulAction Γ X]
variable (ι : Γ →* G) (U : Subgroup G)

/-- View a subgroup of the fixed level as an actual subgroup of the ambient group. -/
abbrev sublevelSubgroup (N : Subgroup U) : Subgroup G := N.map U.subtype

theorem sublevelSubgroup_le (N : Subgroup U) : sublevelSubgroup U N ≤ U := by
  rintro _ ⟨n, _, rfl⟩
  exact n.property

theorem sublevelSubgroup_mono {N P : Subgroup U} (h : N ≤ P) :
    sublevelSubgroup U N ≤ sublevelSubgroup U P :=
  Subgroup.map_mono h

variable (N : Subgroup U) [N.Normal]

/-- Relative normality supplies the conjugation condition for inverse right translation. -/
theorem normalLevel_conjugation (g : U) (k : G) (hk : k ∈ sublevelSubgroup U N) :
    (g : G) * k * (g : G)⁻¹ ∈ sublevelSubgroup U N := by
  obtain ⟨n, hn, rfl⟩ := hk
  exact ⟨g * n * g⁻¹, (inferInstance : N.Normal).conj_mem n hn g, rfl⟩

variable [TopologicalSpace X] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The fixed level acts by inverse right translation on the finer level space. -/
def normalLevelAction : Action TopCat.{max v w} U where
  V := TopCat.of (LevelSpace (X := X) ι (sublevelSubgroup U N))
  ρ :=
    { toFun g := TopCat.ofHom
        ⟨translate (g : G)⁻¹
            (by intro k hk; simpa using normalLevel_conjugation U N g k hk),
          continuous_translate (g : G)⁻¹
            (by intro k hk; simpa using normalLevel_conjugation U N g k hk)⟩
      map_one' := by
        apply TopCat.ext
        intro q
        induction q using Quotient.inductionOn with
        | h x =>
          change mk _ (x.1, x.2 * ((1 : U) : G)⁻¹) = mk _ x
          simp
      map_mul' g h := by
        apply TopCat.ext
        intro q
        induction q using Quotient.inductionOn with
        | h x =>
          change mk _ (x.1, x.2 * ((g * h : U) : G)⁻¹) =
            mk _ (x.1, (x.2 * (h : G)⁻¹) * (g : G)⁻¹)
          simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc] }

@[simp] theorem normalLevelAction_mk (g : U) (x : X × G) :
    End.asHom ((normalLevelAction (X := X) ι U N).ρ g)
        (mk (sublevelSubgroup U N) x) =
      mk (sublevelSubgroup U N) (x.1, x.2 * (g : G)⁻¹) := rfl

/-- Every element of the finer normal level acts trivially on its quotient space. -/
theorem normalLevelAction_kernel : N ≤ (normalLevelAction (X := X) ι U N).ρ.ker := by
  intro n hn
  apply TopCat.ext
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    change mk _ (x.1, x.2 * (n : G)⁻¹) = mk _ x
    apply (mk_eq_mk _ _ _).mpr
    exact ⟨1, (n : G), ⟨n, hn, rfl⟩, by simp, by simp [mul_assoc]⟩

/-- The actual quotient group acts, after factoring the proved trivial normal subgroup. -/
def normalQuotientAction : Action TopCat.{max v w} (U ⧸ N) where
  V := (normalLevelAction (X := X) ι U N).V
  ρ := QuotientGroup.lift N (normalLevelAction (X := X) ι U N).ρ
    (normalLevelAction_kernel (X := X) ι U N)

@[simp] theorem normalQuotientAction_mk (g : U) :
    (normalQuotientAction (X := X) ι U N).ρ (QuotientGroup.mk g) =
      (normalLevelAction (X := X) ι U N).ρ g := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The quotient homomorphism induced by an inclusion of relative normal levels. -/
def normalQuotientMap {P : Subgroup U} [P.Normal] (h : N ≤ P) : U ⧸ N →* U ⧸ P :=
  QuotientGroup.map N P (MonoidHom.id U) h

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] theorem normalQuotientMap_mk {P : Subgroup U} [P.Normal] (h : N ≤ P) (g : U) :
    normalQuotientMap U N h (QuotientGroup.mk g) = QuotientGroup.mk g := rfl

/-- The forgetful map between actual normal-level spaces is quotient-equivariant. -/
def normalCoverMap {P : Subgroup U} [P.Normal] (h : N ≤ P) :
    normalQuotientAction (X := X) ι U N ⟶
      (Action.res TopCat (normalQuotientMap U N h)).obj
        (normalQuotientAction (X := X) ι U P) where
  hom := TopCat.ofHom
    ⟨translate 1 (by intro k hk; simpa using sublevelSubgroup_mono U h hk),
      continuous_translate 1
        (by intro k hk; simpa using sublevelSubgroup_mono U h hk)⟩
  comm g := by
    induction g using QuotientGroup.induction_on with
    | H g =>
      apply TopCat.ext
      intro q
      induction q using Quotient.inductionOn with
      | h x =>
        change mk _ (x.1, (x.2 * (g : G)⁻¹) * 1) =
          mk _ (x.1, (x.2 * 1) * (g : G)⁻¹)
        simp only [mul_one]

@[simp] theorem normalCoverMap_mk {P : Subgroup U} [P.Normal] (h : N ≤ P) (x : X × G) :
    (normalCoverMap (X := X) ι U N h).hom (mk (sublevelSubgroup U N) x) =
      mk (sublevelSubgroup U P) x := by
  change mk _ (x.1, x.2 * 1) = _
  simp

theorem normalCoverMap_surjective {P : Subgroup U} [P.Normal] (h : N ≤ P) :
    Function.Surjective (normalCoverMap (X := X) ι U N h).hom := by
  intro q
  induction q using Quotient.inductionOn with
  | h x => exact ⟨mk _ x, normalCoverMap_mk ι U N h x⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] theorem normalQuotientMap_refl :
    normalQuotientMap U N (le_refl N) = MonoidHom.id (U ⧸ N) :=
  QuotientGroup.map_id _ _

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] theorem normalQuotientMap_comp {P Q : Subgroup U} [P.Normal] [Q.Normal]
    (h : N ≤ P) (h' : P ≤ Q) :
    (normalQuotientMap U P h').comp (normalQuotientMap U N h) =
      normalQuotientMap U N (h.trans h') := by
  simpa only [normalQuotientMap, MonoidHom.id_comp] using
    QuotientGroup.map_comp_map N P Q (MonoidHom.id U) (MonoidHom.id U) h h'

@[simp] theorem normalCoverMap_refl :
    (normalCoverMap (X := X) ι U N (le_refl N)).hom =
      𝟙 (normalQuotientAction (X := X) ι U N).V := by
  apply TopCat.ext
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    change mk _ (x.1, x.2 * 1) = mk _ x
    simp only [mul_one]

@[reassoc] theorem normalCoverMap_comp {P Q : Subgroup U} [P.Normal] [Q.Normal]
    (h : N ≤ P) (h' : P ≤ Q) :
    (normalCoverMap (X := X) ι U N h).hom ≫ (normalCoverMap (X := X) ι U P h').hom =
      (normalCoverMap (X := X) ι U N (h.trans h')).hom := by
  apply TopCat.ext
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    change mk _ (x.1, (x.2 * 1) * 1) = mk _ (x.1, x.2 * 1)
    simp only [mul_one]

/-- The continuous forgetful projection to the original level. -/
def normalCoverProjection :
    (normalQuotientAction (X := X) ι U N).V ⟶ TopCat.of (LevelSpace (X := X) ι U) :=
  TopCat.ofHom
    ⟨translate 1 (by intro k hk; simpa using sublevelSubgroup_le U N hk),
      continuous_translate 1 (by intro k hk; simpa using sublevelSubgroup_le U N hk)⟩

@[simp] theorem normalCoverProjection_mk (x : X × G) :
    normalCoverProjection (X := X) ι U N (mk (sublevelSubgroup U N) x) = mk U x := by
  change mk U (x.1, x.2 * 1) = mk U x
  simp only [mul_one]

theorem normalCoverProjection_surjective :
    Function.Surjective (normalCoverProjection (X := X) ι U N) := by
  intro q
  induction q using Quotient.inductionOn with
  | h x => exact ⟨mk _ x, normalCoverProjection_mk ι U N x⟩

/-- Every residual quotient action preserves the projection to the base level. -/
@[reassoc] theorem normalCoverProjection_invariant (g : U ⧸ N) :
    End.asHom ((normalQuotientAction (X := X) ι U N).ρ g) ≫
      normalCoverProjection (X := X) ι U N =
        normalCoverProjection (X := X) ι U N := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    apply TopCat.ext
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      change mk U (x.1, (x.2 * (g : G)⁻¹) * 1) = mk U (x.1, x.2 * 1)
      simp only [mul_one]
      apply (mk_eq_mk _ _ _).mpr
      exact ⟨1, (g : G), g.property, by simp, by simp [mul_assoc]⟩

@[reassoc] theorem normalCoverMap_projection {P : Subgroup U} [P.Normal] (h : N ≤ P) :
    (normalCoverMap (X := X) ι U N h).hom ≫ normalCoverProjection (X := X) ι U P =
      normalCoverProjection (X := X) ι U N := by
  apply TopCat.ext
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    change mk U (x.1, (x.2 * 1) * 1) = mk U (x.1, x.2 * 1)
    simp only [mul_one]

end Langlands.Shimura.LevelSpace
