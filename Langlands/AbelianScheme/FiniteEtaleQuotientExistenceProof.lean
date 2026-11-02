import Langlands.AbelianScheme.FiniteEtaleQuotientExistenceStatement
import Langlands.AbelianScheme.FiniteEtaleQuotientPropertyDescent
import Langlands.AlgebraicGeometry.RelativeProjectiveSpaceFibreAffineOpen
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation
import Langlands.AnthropicFLT.OverBase.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Langlands.AnthropicFLT.OverBase.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid
import Langlands.AnthropicFLT.OverBase.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Quotients of abelian schemes by finite étale subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry NeronModelInfra GroupLawOverBase
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.FiniteEtaleQuotientExistence

variable {S : Scheme.{u}}

/-- Composition of a point over `t` with a morphism `ψ` over `S`. -/
def mapPt {D E : Scheme.{u}} {gD : D ⟶ S} {gE : E ⟶ S} (ψ : D ⟶ E) (hψ : ψ ≫ gE = gD)
    {T : Scheme.{u}} {t : T ⟶ S} (x : SchemeHomOver t gD) : SchemeHomOver t gE :=
  ⟨x.1 ≫ ψ, by rw [Category.assoc, hψ, x.2]⟩

theorem overHomEquivSchemeHomOver_comp_homMk {D E : Scheme.{u}} {gD : D ⟶ S} {gE : E ⟶ S}
    (ψ : D ⟶ E) (hψ : ψ ≫ gE = gD) (T : Over S) (a : T ⟶ Over.mk gD) :
    overHomEquivSchemeHomOver T gE (a ≫ Over.homMk ψ hψ) =
      mapPt ψ hψ (overHomEquivSchemeHomOver T gD a) := by
  apply Subtype.ext
  simp [overHomEquivSchemeHomOver, mapPt]

/-- A morphism over `S` from a group object of `Over S` to a scheme with a relative group law is
a monoid homomorphism for the induced group object as soon as it is multiplicative on points. -/
theorem isMonHom_homMk {D E : Scheme.{u}} {gD : D ⟶ S} {gE : E ⟶ S} [GrpObj (Over.mk gD)]
    (LE : RelativeGroupLaw S gE) (ψ : D ⟶ E) (hψ : ψ ≫ gE = gD)
    (ψ_hom : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t gD),
      mapPt ψ hψ ((relativeGroupLawOfGrpObj S gD).mul t x y) =
        LE.mul t (mapPt ψ hψ x) (mapPt ψ hψ y)) :
    letI := LE.grpObjOverMk
    IsMonHom (Over.homMk ψ hψ : Over.mk gD ⟶ Over.mk gE) := by
  let _ := LE.grpObjOverMk
  have src_mul : ∀ (T : Over S) (a b : T ⟶ Over.mk gD),
      overHomEquivSchemeHomOver T gD (a * b) =
        (relativeGroupLawOfGrpObj S gD).mul T.hom (overHomEquivSchemeHomOver T gD a)
          (overHomEquivSchemeHomOver T gD b) := fun _ _ _ => rfl
  have src_one : ∀ (T : Over S), overHomEquivSchemeHomOver T gD (1 : T ⟶ Over.mk gD) =
      (relativeGroupLawOfGrpObj S gD).one T.hom := fun _ => rfl
  have hone : ∀ (T : Over S),
      mapPt ψ hψ ((relativeGroupLawOfGrpObj S gD).one T.hom) = LE.one T.hom := by
    intro T
    have h' := ψ_hom T.hom ((relativeGroupLawOfGrpObj S gD).one T.hom)
      ((relativeGroupLawOfGrpObj S gD).one T.hom)
    rw [RelativeGroupLaw.one_mul] at h'
    have := congrArg (LE.mul T.hom (LE.inv T.hom (mapPt ψ hψ
      ((relativeGroupLawOfGrpObj S gD).one T.hom)))) h'
    rw [← LE.mul_assoc, LE.inv_mul_cancel, LE.one_mul] at this
    exact this.symm
  refine ⟨?_, ?_⟩
  · apply (overHomEquivSchemeHomOver (𝟙_ (Over S)) gE).injective
    rw [overHomEquivSchemeHomOver_comp_homMk, MonObj.one_eq_one, MonObj.one_eq_one, src_one,
      LE.overHomEquivSchemeHomOver_one]
    exact hone _
  · apply (overHomEquivSchemeHomOver (Over.mk gD ⊗ Over.mk gD) gE).injective
    rw [overHomEquivSchemeHomOver_comp_homMk, MonObj.mul_eq_mul, MonObj.mul_eq_mul, src_mul,
      ψ_hom, ← overHomEquivSchemeHomOver_comp_homMk, ← overHomEquivSchemeHomOver_comp_homMk,
      MonObj.comp_mul, LE.overHomEquivSchemeHomOver_mul, tensorHom_fst, tensorHom_snd]

/-- Quotient data exist for every finite étale subgroup of an abelian scheme over a locally
noetherian base in which every finite subset of a fibre lies in an affine open. -/
theorem nonempty_quotientData_of_forall_finset_fibre [IsLocallyNoetherian S]
    (A : AbelianScheme S)
    (hfib : ∀ (F : Finset A.X.left) (s : S), (∀ x ∈ F, A.X.hom x = s) →
      ∃ W : A.X.left.Opens, IsAffineOpen W ∧ ∀ x ∈ F, x ∈ W)
    (K : FiniteEtaleSubgroup A) : Nonempty K.QuotientData := by
  classical
  let iA : GrpObj (Over.mk A.X.hom) := A.grp
  let L : RelativeGroupLaw S A.X.hom := relativeGroupLawOfGrpObj S A.X.hom
  let j : K.G.X.left ⟶ A.X.left := CommGroupScheme.hom K.inclusion
  have hjf : j ≫ A.X.hom = K.G.X.hom := Over.w (CommGroupScheme.groupHom K.inclusion).hom.hom
  have : IsFinite (j ≫ A.X.hom) := by rw [hjf]; infer_instance
  have : Flat (j ≫ A.X.hom) := by rw [hjf]; infer_instance
  have : LocallyOfFinitePresentation (j ≫ A.X.hom) := by rw [hjf]; infer_instance
  have : Etale (j ≫ A.X.hom) := by rw [hjf]; infer_instance
  -- `K` is stable under the group law of `A`.
  have hE_one : ∀ {T : Scheme.{u}} (t : T ⟶ S),
      ∃ e : T ⟶ K.G.X.left, e ≫ j = (L.one t).1 := by
    intro T t
    refine ⟨(1 : Over.mk t ⟶ K.G.X).left, ?_⟩
    rw [← Over.comp_left, MonObj.one_comp]
    rfl
  have hE_mul : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t A.X.hom),
      (∃ e₁ : T ⟶ K.G.X.left, e₁ ≫ j = x.1) → (∃ e₂ : T ⟶ K.G.X.left, e₂ ≫ j = y.1) →
        ∃ e : T ⟶ K.G.X.left, e ≫ j = (L.mul t x y).1 := by
    rintro T t x y ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
    have w₁ : e₁ ≫ K.G.X.hom = t := by rw [← hjf, ← Category.assoc, h₁, x.2]
    have w₂ : e₂ ≫ K.G.X.hom = t := by rw [← hjf, ← Category.assoc, h₂, y.2]
    refine ⟨((Over.homMk e₁ w₁ : Over.mk t ⟶ K.G.X) * Over.homMk e₂ w₂).left, ?_⟩
    rw [← Over.comp_left, MonObj.mul_comp]
    have ha : (Over.homMk e₁ w₁ : Over.mk t ⟶ K.G.X) ≫
        (CommGroupScheme.groupHom K.inclusion).hom.hom = schemeHomOverToOverHom x := by
      ext; simpa using h₁
    have hb : (Over.homMk e₂ w₂ : Over.mk t ⟶ K.G.X) ≫
        (CommGroupScheme.groupHom K.inclusion).hom.hom = schemeHomOverToOverHom y := by
      ext; simpa using h₂
    rw [ha, hb]
    rfl
  have hE_inv : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t A.X.hom),
      (∃ e₁ : T ⟶ K.G.X.left, e₁ ≫ j = x.1) → ∃ e : T ⟶ K.G.X.left, e ≫ j = (L.inv t x).1 := by
    rintro T t x ⟨e₁, h₁⟩
    have w₁ : e₁ ≫ K.G.X.hom = t := by rw [← hjf, ← Category.assoc, h₁, x.2]
    refine ⟨((Over.homMk e₁ w₁ : Over.mk t ⟶ K.G.X)⁻¹).left, ?_⟩
    rw [← Over.comp_left, GrpObj.inv_comp]
    have ha : (Over.homMk e₁ w₁ : Over.mk t ⟶ K.G.X) ≫
        (CommGroupScheme.groupHom K.inclusion).hom.hom = schemeHomOverToOverHom x := by
      ext; simpa using h₁
    rw [ha]
    rfl
  have hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t A.X.hom),
      L.mul t x y = L.mul t y x :=
    fun t x y => relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj A.comm t x y
  -- The action of `K` on `A` is a finite locally free equivalence relation.
  obtain ⟨hsF, hsFl, hsL, htF, htFl, htL, hmono, hequiv⟩ :=
    L.finiteLocallyFree_mono_equivalence_actionGroupoid j hE_one hE_mul hE_inv
  -- Its classes lie in fibres of `A`, hence in affine opens.
  have haff : ∀ x : A.X.left, ∃ U : A.X.left.Opens, IsAffineOpen U ∧
      ∀ r : ↥(pullback (j ≫ A.X.hom) A.X.hom),
        pullback.snd (j ≫ A.X.hom) A.X.hom r = x → L.action j r ∈ U := by
    intro x
    have hfin : (pullback.snd (j ≫ A.X.hom) A.X.hom ⁻¹' {x}).Finite :=
      (pullback.snd (j ≫ A.X.hom) A.X.hom).finite_preimage_singleton x
    obtain ⟨W, hW, hFW⟩ := hfib (hfin.image (L.action j)).toFinset (A.X.hom x) (by
      intro y hy
      rw [Set.Finite.mem_toFinset] at hy
      obtain ⟨r, hr, rfl⟩ := hy
      rw [← Scheme.Hom.comp_apply, L.action_over j, Scheme.Hom.comp_apply]
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hr
      rw [hr])
    exact ⟨W, hW, fun r hr => hFW _ (by rw [Set.Finite.mem_toFinset]; exact ⟨r, hr, rfl⟩)⟩
  -- The quotient scheme.
  obtain ⟨P, p, w, hpF, hpFl, hpL, hpS, hR, ⟨hcoeq⟩⟩ :=
    Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation
      (pullback.snd (j ≫ A.X.hom) A.X.hom) (L.action j) hmono hequiv haff
  -- Its group law.
  obtain ⟨g, hg, LP, hmul, hcommP, hker⟩ :=
    L.exists_relativeGroupLaw_quotient_of_isColimit j hE_one hE_mul hE_inv hcomm p w hR hcoeq
  let iP : GrpObj (Over.mk g) := LP.grpObjOverMk
  have hPcomm : IsCommMonObj (Over.mk g) := LP.isCommMonObj_grpObjOverMk_iff_mul_comm.2 hcommP
  let B : CommGroupScheme S := { X := Over.mk g, grp := iP, comm := hPcomm }
  have hφ : IsMonHom (Over.homMk p hg : Over.mk A.X.hom ⟶ Over.mk g) :=
    isMonHom_homMk LP p hg hmul
  let qB : A.toCommGroupScheme ⟶ B :=
    Additive.ofMul (Grp.homMk (A := A.toGrp) (B := B.toGrp) (Over.homMk p hg))
  -- `p` is étale by flat descent along itself.
  have hpEt : Etale p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hR ⟨⟨hpS, hpFl⟩, inferInstance⟩
      (inferInstanceAs (Etale (pullback.snd (j ≫ A.X.hom) A.X.hom)))
  -- The kernel square.
  have hone : ∀ {T : Scheme.{u}} (t : T ⟶ S), (LP.one t).1 = t ≫ η[Over.mk g].left := by
    intro T t
    rw [← LP.overHomToSchemeHomOver_one t]
    rfl
  have hηg : η[Over.mk g].left ≫ g = 𝟙 S := Over.w η[Over.mk g]
  have hsq : ∀ {T : Scheme.{u}} (a : T ⟶ A.X.left) (b : T ⟶ S),
      a ≫ p = b ≫ η[Over.mk g].left → ∃ e : T ⟶ K.G.X.left, e ≫ j = a := by
    intro T a b hab
    have hb : a ≫ A.X.hom = b := by
      rw [← hg, ← Category.assoc, hab, Category.assoc, hηg, Category.comp_id]
    refine (hker (a ≫ A.X.hom) ⟨a, rfl⟩).1 (Subtype.ext ?_)
    change a ≫ p = (LP.one (a ≫ A.X.hom)).1
    rw [hone, hb, hab]
  have hcommsq : j ≫ p = K.G.X.hom ≫ η[Over.mk g].left := by
    have := (hker (j ≫ A.X.hom) ⟨j, rfl⟩).2 ⟨𝟙 _, Category.id_comp _⟩
    have h1 := congrArg Subtype.val this
    change j ≫ p = (LP.one (j ≫ A.X.hom)).1 at h1
    rw [h1, hone, hjf]
  refine ⟨{ B := ofFiniteEtaleSurjective A B p hg
            q := qB
            isFinite := hpF
            etale := hpEt
            surjective := hpS
            isPullback := ?_ }⟩
  refine ⟨⟨hcommsq⟩, ⟨PullbackCone.IsLimit.mk hcommsq
    (fun c => Classical.choose (hsq c.fst c.snd c.condition))
    (fun c => Classical.choose_spec (hsq c.fst c.snd c.condition)) (fun c => ?_)
    (fun c m h₁ _ => ?_)⟩⟩
  · rw [← hjf, ← Category.assoc, Classical.choose_spec (hsq c.fst c.snd c.condition)]
    rw [← hg, ← Category.assoc, c.condition, Category.assoc, hηg, Category.comp_id]
  · rw [← cancel_mono j, h₁, Classical.choose_spec (hsq c.fst c.snd c.condition)]

end Langlands.AbelianScheme.FiniteEtaleQuotientExistence

namespace Langlands.AbelianScheme

/-- Over a locally noetherian base, every finite étale subgroup of a projectively embedded
abelian scheme has quotient data. -/
theorem finiteEtaleQuotientExistence : FiniteEtaleQuotientExistenceStatement.{u} := by
  intro S _ A n i _ hi K
  exact FiniteEtaleQuotientExistence.nonempty_quotientData_of_forall_finset_fibre A
    (fun F s hF =>
      Langlands.AlgebraicGeometry.RelativeProjectiveSpace.exists_isAffineOpen_forall_mem_of_fibre
        A.X.hom n i hi F s hF) K

end Langlands.AbelianScheme
