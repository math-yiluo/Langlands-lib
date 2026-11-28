import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.Subgroup.Center

/-! # Pushout of a central group extension along a map into a center -/

namespace Langlands.GroupTheory

open scoped IsMulCommutative

variable {A E B D H : Type*} [Group A] [Group E] [Group B] [Group D] [Group H]
variable (S : GroupExtension A E B) (hS : S.inl.range ≤ Subgroup.center E)
  (j : A →* Subgroup.center D)

/-- The central relation consisting of the pairs `(j(a)⁻¹, S.inl a)`. -/
def centralPushoutRelation : Subgroup (D × E) :=
  let i : A →* Subgroup.center E := S.inl.codRestrict _ (fun a => hS ⟨a, rfl⟩)
  (((Subgroup.center D).subtype.comp (invMonoidHom.comp j)).prod
    ((Subgroup.center E).subtype.comp i)).range

theorem mem_centralPushoutRelation (z : D × E) :
    z ∈ centralPushoutRelation S hS j ↔ ∃ a : A, ((j a : D)⁻¹, S.inl a) = z :=
  Iff.rfl

theorem centralPushoutRelation_le_center :
    centralPushoutRelation S hS j ≤ Subgroup.center (D × E) := by
  intro z hz
  obtain ⟨a, rfl⟩ := (mem_centralPushoutRelation S hS j z).mp hz
  rw [Subgroup.center_prod]
  exact ⟨(Subgroup.center D).inv_mem (j a).property, hS ⟨a, rfl⟩⟩

instance centralPushoutRelation_normal : (centralPushoutRelation S hS j).Normal :=
  Subgroup.normal_of_le_center (centralPushoutRelation_le_center S hS j)

/-- The quotient of `D × E` that identifies the two images of `A`. -/
abbrev CentralPushout := (D × E) ⧸ centralPushoutRelation S hS j

/-- The quotient homomorphism from the direct product. -/
def centralPushoutQuotient : D × E →* CentralPushout S hS j :=
  QuotientGroup.mk' _

/-- The map from the new kernel, induced by `d ↦ (d, 1)`. -/
def centralPushoutInl : D →* CentralPushout S hS j :=
  (centralPushoutQuotient S hS j).comp (MonoidHom.inl D E)

/-- The map from the old middle group, induced by `e ↦ (1, e)`. -/
def centralPushoutFromOld : E →* CentralPushout S hS j :=
  (centralPushoutQuotient S hS j).comp (MonoidHom.inr D E)

/-- The maps from the new kernel and the old middle group agree on `A`. -/
theorem centralPushout_agree :
    (centralPushoutInl S hS j).comp ((Subgroup.center D).subtype.comp j) =
      (centralPushoutFromOld S hS j).comp S.inl := by
  apply MonoidHom.ext
  intro a
  change centralPushoutQuotient S hS j (j a, 1) =
    centralPushoutQuotient S hS j (1, S.inl a)
  apply (QuotientGroup.eq_iff_div_mem).mpr
  exact (mem_centralPushoutRelation S hS j _).mpr ⟨a⁻¹, by simp⟩

/-- The images of the two factors commute elementwise. -/
theorem centralPushout_commute (d : D) (e : E) :
    Commute (centralPushoutInl S hS j d) (centralPushoutFromOld S hS j e) :=
  (MonoidHom.commute_inl_inr d e).map (centralPushoutQuotient S hS j)

/-- The two factor maps generate the class of each pair. -/
theorem centralPushoutQuotient_pair (d : D) (e : E) :
    centralPushoutQuotient S hS j (d, e) =
      centralPushoutInl S hS j d * centralPushoutFromOld S hS j e := by
  change centralPushoutQuotient S hS j (d, e) =
    centralPushoutQuotient S hS j (d, 1) * centralPushoutQuotient S hS j (1, e)
  rw [← map_mul, Prod.fst_mul_snd (d, e)]

/-- The projection induced by `(d, e) ↦ S.rightHom e`. -/
def centralPushoutProjection : CentralPushout S hS j →* B :=
  QuotientGroup.lift _ (S.rightHom.comp (MonoidHom.snd D E)) (by
    intro z hz
    obtain ⟨a, rfl⟩ := (mem_centralPushoutRelation S hS j z).mp hz
    exact S.rightHom_inl a)

@[simp] theorem centralPushoutProjection_quotient (z : D × E) :
    centralPushoutProjection S hS j (centralPushoutQuotient S hS j z) = S.rightHom z.2 :=
  rfl

@[simp] theorem centralPushoutProjection_comp_inl :
    (centralPushoutProjection S hS j).comp (centralPushoutInl S hS j) = 1 := by
  ext d
  exact map_one S.rightHom

@[simp] theorem centralPushoutProjection_comp_fromOld :
    (centralPushoutProjection S hS j).comp (centralPushoutFromOld S hS j) = S.rightHom :=
  rfl

/-- Pushing out along `j` gives an extension of `B` by `D`. -/
def centralPushoutExtension : GroupExtension D (CentralPushout S hS j) B where
  inl := centralPushoutInl S hS j
  rightHom := centralPushoutProjection S hS j
  inl_injective := by
    apply (injective_iff_map_eq_one _).mpr
    intro d hd
    change centralPushoutQuotient S hS j (d, 1) = 1 at hd
    have hrel : (d, (1 : E)) ∈ centralPushoutRelation S hS j :=
      (QuotientGroup.eq_one_iff _).mp hd
    obtain ⟨a, ha⟩ := (mem_centralPushoutRelation S hS j _).mp hrel
    have ha₁ : a = 1 := (map_eq_one_iff S.inl S.inl_injective).mp (congrArg Prod.snd ha)
    simpa [ha₁] using (congrArg Prod.fst ha).symm
  range_inl_eq_ker_rightHom := by
    apply Subgroup.ext
    intro z
    rw [MonoidHom.mem_ker]
    constructor
    · rintro ⟨d, rfl⟩
      exact DFunLike.congr_fun (centralPushoutProjection_comp_inl S hS j) d
    · obtain ⟨⟨d, e⟩, rfl⟩ := QuotientGroup.mk'_surjective (centralPushoutRelation S hS j) z
      intro hz
      change S.rightHom e = 1 at hz
      obtain ⟨a, rfl⟩ : e ∈ S.inl.range := by
        simpa only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker] using hz
      have ha : centralPushoutInl S hS j (j a) = centralPushoutFromOld S hS j (S.inl a) :=
        DFunLike.congr_fun (centralPushout_agree S hS j) a
      refine ⟨d * (j a : D), ?_⟩
      change centralPushoutInl S hS j (d * (j a : D)) =
        centralPushoutQuotient S hS j (d, S.inl a)
      rw [centralPushoutQuotient_pair, map_mul, ha]
  rightHom_surjective := by
    intro b
    obtain ⟨e, he⟩ := S.rightHom_surjective b
    exact ⟨centralPushoutFromOld S hS j e, he⟩

/-- Commuting maps from `D` and `E` that agree on `A` descend to the quotient. -/
def centralPushoutLift (u : D →* H) (v : E →* H) (comm : ∀ d e, Commute (u d) (v e))
    (agree : u.comp ((Subgroup.center D).subtype.comp j) = v.comp S.inl) :
    CentralPushout S hS j →* H :=
  QuotientGroup.lift _ (u.noncommCoprod v comm) (by
    intro z hz
    obtain ⟨a, rfl⟩ := (mem_centralPushoutRelation S hS j z).mp hz
    have ha : u (j a) = v (S.inl a) := DFunLike.congr_fun agree a
    change u ((j a : D)⁻¹) * v (S.inl a) = 1
    rw [map_inv, ha, inv_mul_cancel])

@[simp] theorem centralPushoutLift_quotient (u : D →* H) (v : E →* H)
    (comm : ∀ d e, Commute (u d) (v e))
    (agree : u.comp ((Subgroup.center D).subtype.comp j) = v.comp S.inl) (z : D × E) :
    centralPushoutLift S hS j u v comm agree (centralPushoutQuotient S hS j z) =
      u z.1 * v z.2 := rfl

@[simp] theorem centralPushoutLift_comp_inl (u : D →* H) (v : E →* H)
    (comm : ∀ d e, Commute (u d) (v e))
    (agree : u.comp ((Subgroup.center D).subtype.comp j) = v.comp S.inl) :
    (centralPushoutLift S hS j u v comm agree).comp (centralPushoutInl S hS j) = u := by
  ext d
  change u d * v 1 = u d
  rw [map_one, mul_one]

@[simp] theorem centralPushoutLift_comp_fromOld (u : D →* H) (v : E →* H)
    (comm : ∀ d e, Commute (u d) (v e))
    (agree : u.comp ((Subgroup.center D).subtype.comp j) = v.comp S.inl) :
    (centralPushoutLift S hS j u v comm agree).comp (centralPushoutFromOld S hS j) = v := by
  ext e
  change u 1 * v e = v e
  rw [map_one, one_mul]

/-- Each map on the quotient is determined by its restrictions to the factors. -/
theorem centralPushout_hom_ext {u v : CentralPushout S hS j →* H}
    (hD : u.comp (centralPushoutInl S hS j) = v.comp (centralPushoutInl S hS j))
    (hE : u.comp (centralPushoutFromOld S hS j) = v.comp (centralPushoutFromOld S hS j)) :
    u = v := by
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  rintro ⟨d, e⟩
  change u (centralPushoutQuotient S hS j (d, e)) = v (centralPushoutQuotient S hS j (d, e))
  rw [centralPushoutQuotient_pair, map_mul, map_mul]
  exact congrArg₂ (· * ·) (DFunLike.congr_fun hD d) (DFunLike.congr_fun hE e)

end Langlands.GroupTheory
