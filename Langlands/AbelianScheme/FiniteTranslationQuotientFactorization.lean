import Langlands.AbelianScheme.FiniteEtaleQuotientExistenceProof
import Langlands.GroupScheme.FppfQuotientTargetSmooth

/-! # Factoring a finite map through its translation symmetries -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  NeronModelInfra GroupLawOverBase
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

/-- An invariant finite map out of an abelian variety over a field descends through
an abelian variety quotient that kills the given finite closed subgroup. -/
abbrev FiniteTranslationQuotientFactorizationStatement : Prop :=
  ∀ {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))
    {H : GroupScheme (Spec (CommRingCat.of K))} (i : H ⟶ A.toGrp)
    [IsClosedImmersion i.hom.hom.left] [IsFinite H.X.hom]
    {W : Over (Spec (CommRingCat.of K))} (F : A.X ⟶ W) [IsFinite F.left],
    (∀ (T : Over (Spec (CommRingCat.of K))) (h : T ⟶ H.X) (a : T ⟶ A.X),
      ((h ≫ i.hom.hom) * a) ≫ F = a ≫ F) →
    ∃ (B : AbelianScheme (Spec (CommRingCat.of K))) (q : A.X ⟶ B.X) (b : B.X ⟶ W),
      IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ q ≫ b = F ∧
      i.hom.hom ≫ q = (1 : H.X ⟶ A.X) ≫ q

set_option backward.isDefEq.respectTransparency.types false in
/-- The affine inverse images under the finite map contain the orbits. The
finite locally free equivalence relation thus has an effective quotient. -/
theorem finiteTranslationQuotientFactorization : FiniteTranslationQuotientFactorizationStatement.{u} := by
  intro K _ A H i _ _ W F _ hinv
  let S := Spec (CommRingCat.of K)
  let iA : GrpObj (Over.mk A.X.hom) := A.grp
  let L : RelativeGroupLaw S A.X.hom := relativeGroupLawOfGrpObj S A.X.hom
  let j := i.hom.hom.left
  have hjf : j ≫ A.X.hom = H.X.hom := Over.w i.hom.hom
  have : IsFinite (j ≫ A.X.hom) := hjf ▸ inferInstanceAs (IsFinite H.X.hom)
  have : Flat (j ≫ A.X.hom) := inferInstance
  have : LocallyOfFinitePresentation (j ≫ A.X.hom) := inferInstance
  have hE_one : ∀ {T : Scheme.{u}} (t : T ⟶ S),
      ∃ e : T ⟶ H.X.left, e ≫ j = (L.one t).1 := by
    intro T t
    refine ⟨(1 : Over.mk t ⟶ H.X).left, ?_⟩
    rw [← Over.comp_left, MonObj.one_comp]
    rfl
  have hE_mul : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t A.X.hom),
      (∃ e₁ : T ⟶ H.X.left, e₁ ≫ j = x.1) → (∃ e₂ : T ⟶ H.X.left, e₂ ≫ j = y.1) →
        ∃ e : T ⟶ H.X.left, e ≫ j = (L.mul t x y).1 := by
    rintro T t x y ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
    have w₁ : e₁ ≫ H.X.hom = t := by rw [← hjf, ← Category.assoc, h₁, x.2]
    have w₂ : e₂ ≫ H.X.hom = t := by rw [← hjf, ← Category.assoc, h₂, y.2]
    let a : Over.mk t ⟶ H.X := Over.homMk e₁ w₁
    let b : Over.mk t ⟶ H.X := Over.homMk e₂ w₂
    have ha : a ≫ i.hom.hom = schemeHomOverToOverHom x := Over.OverMorphism.ext h₁
    have hb : b ≫ i.hom.hom = schemeHomOverToOverHom y := Over.OverMorphism.ext h₂
    refine ⟨(a * b).left, ?_⟩
    rw [← Over.comp_left, MonObj.mul_comp, ha, hb]
    rfl
  have hE_inv : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t A.X.hom),
      (∃ e : T ⟶ H.X.left, e ≫ j = x.1) → ∃ e : T ⟶ H.X.left, e ≫ j = (L.inv t x).1 := by
    rintro T t x ⟨e, he⟩
    have w : e ≫ H.X.hom = t := by rw [← hjf, ← Category.assoc, he, x.2]
    let a : Over.mk t ⟶ H.X := Over.homMk e w
    have ha : a ≫ i.hom.hom = schemeHomOverToOverHom x := Over.OverMorphism.ext he
    refine ⟨a⁻¹.left, ?_⟩
    rw [← Over.comp_left, GrpObj.inv_comp, ha]
    rfl
  have hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t A.X.hom),
      L.mul t x y = L.mul t y x :=
    fun t x y ↦ relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj A.comm t x y
  let s := pullback.snd (j ≫ A.X.hom) A.X.hom
  have hF : s ≫ F.left = L.action j ≫ F.left := by
    let T := Over.mk (s ≫ A.X.hom)
    let h : T ⟶ H.X := Over.homMk (pullback.fst (j ≫ A.X.hom) A.X.hom) (by
      change pullback.fst (j ≫ A.X.hom) A.X.hom ≫ H.X.hom = s ≫ A.X.hom
      rw [← hjf, pullback.condition])
    let a : T ⟶ A.X := Over.homMk s rfl
    exact (congrArg (fun v ↦ v.left) (hinv T h a)).symm
  obtain ⟨hsF, hsFl, hsL, htF, htFl, htL, hmono, hequiv⟩ :=
    L.finiteLocallyFree_mono_equivalence_actionGroupoid j hE_one hE_mul hE_inv
  have haff (x : A.X.left) : ∃ U : A.X.left.Opens, IsAffineOpen U ∧
      ∀ r : ↥(pullback (j ≫ A.X.hom) A.X.hom), s r = x → L.action j r ∈ U := by
    have hx : F.left x ∈ (Set.univ : Set W.left) := Set.mem_univ _
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      W.left.isBasis_affineOpens.exists_subset_of_mem_open hx isOpen_univ
    refine ⟨F.left ⁻¹ᵁ V, hV.preimage F.left, fun r hr ↦ ?_⟩
    change F.left (L.action j r) ∈ V
    rw [← Scheme.Hom.comp_apply, ← hF, Scheme.Hom.comp_apply, hr]
    exact hxV
  obtain ⟨P, p, w, hpF, hpFl, hpL, hpS, hR, ⟨hcoeq⟩⟩ :=
    Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation s (L.action j) hmono hequiv haff
  obtain ⟨g, hg, LP, hmul, hcommP, hker⟩ :=
    L.exists_relativeGroupLaw_quotient_of_isColimit j hE_one hE_mul hE_inv hcomm p w hR hcoeq
  let iP : GrpObj (Over.mk g) := LP.grpObjOverMk
  have hPcomm : IsCommMonObj (Over.mk g) := LP.isCommMonObj_grpObjOverMk_iff_mul_comm.2 hcommP
  let B₀ : CommGroupScheme S := { X := Over.mk g, grp := iP, comm := hPcomm }
  have hφ : IsMonHom (Over.homMk p hg : Over.mk A.X.hom ⟶ Over.mk g) :=
    FiniteEtaleQuotientExistence.isMonHom_homMk LP p hg hmul
  let qG : A.toGrp ⟶ B₀.toGrp := Grp.homMk (A := A.toGrp) (B := B₀.toGrp) (Over.homMk p hg)
  have : Flat qG.hom.hom.left := hpFl
  have : Surjective qG.hom.hom.left := hpS
  have : LocallyOfFinitePresentation qG.hom.hom.left := hpL
  have hSmooth : Smooth g := GroupScheme.smooth_target_of_surjective_flat_hom qG
  have : IsSeparated (p ≫ g) := hg ▸ inferInstanceAs (IsSeparated A.X.hom)
  have : IsSeparated g :=
    FiniteEtaleQuotientPropertyDescent.isSeparated_of_comp_of_surjective_of_universallyClosed p g
  have : UniversallyClosed (p ≫ g) := hg ▸ inferInstanceAs (UniversallyClosed A.X.hom)
  have : UniversallyClosed g := UniversallyClosed.of_comp_surjective p g
  have : GeometricallyConnected (p ≫ g) := hg ▸ inferInstanceAs (GeometricallyConnected A.X.hom)
  let B : AbelianScheme S :=
    { B₀ with
      smooth := hSmooth
      proper := (isProper_iff g).mpr ⟨inferInstance, inferInstance, inferInstance⟩
      geometricallyConnected :=
        FiniteEtaleQuotientPropertyDescent.geometricallyConnected_of_comp_of_surjective p g }
  let b := Cofork.IsColimit.desc hcoeq F.left hF
  have hb : p ≫ b = F.left := Cofork.IsColimit.π_desc hcoeq
  have hb_over : b ≫ W.hom = g := by
    apply Cofork.IsColimit.hom_ext hcoeq
    change p ≫ b ≫ W.hom = p ≫ g
    rw [← Category.assoc, hb, Over.w F, hg]
  refine ⟨B, Over.homMk p hg, Over.homMk b hb_over, hpF, hpFl, hpS,
    Over.OverMorphism.ext hb, ?_⟩
  have hi := (hker H.X.hom ⟨j, hjf⟩).mpr ⟨𝟙 _, Category.id_comp _⟩
  have h1 := (hker H.X.hom (L.one H.X.hom)).mpr (hE_one H.X.hom)
  exact Over.OverMorphism.ext (congrArg Subtype.val (hi.trans h1.symm))

end Langlands.AbelianScheme
