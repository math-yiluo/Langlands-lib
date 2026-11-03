import Langlands.GroupScheme.Absolute.FiniteIndexQuotientProperStatement
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-! # Proof of the properness transfer to quotients by open subgroups of stabilizers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace FiniteIndexTransfer

section Schemes

/-- A morphism from a reduced scheme whose image lies in the image of a closed immersion factors
through the closed immersion. -/
theorem exists_lift_of_range_subset {X Y Z : Scheme.{u}} (i : X ⟶ Z) [IsClosedImmersion i]
    (g : Y ⟶ Z) [IsReduced Y] (h : Set.range g ⊆ Set.range i) : ∃ l : Y ⟶ X, l ≫ i = g := by
  have : Surjective (pullback.snd i g) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨x, hx⟩ := h ⟨y, rfl⟩
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback x y hx
    exact ⟨z, hz⟩
  have : IsIso (pullback.snd i g) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.snd i g) ≫ pullback.fst i g, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

/-- Finitely many sections of `p` give a finite morphism to the source of `p` whose image
contains all their images. -/
theorem exists_isFinite_cover {Y Z : Scheme.{u}} (p : Y ⟶ Z) {I : Type*} (σ : I → (Z ⟶ Y))
    (hσ : ∀ i, σ i ≫ p = 𝟙 Z) (s : Finset I) (hs : s.Nonempty) :
    ∃ (X : Scheme.{u}) (e : X ⟶ Y), IsFinite (e ≫ p) ∧
      ∀ i ∈ s, Set.range (σ i) ⊆ Set.range e := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    refine ⟨Z, σ a, by rw [hσ]; infer_instance, ?_⟩
    intro i hi
    rw [Finset.mem_singleton.mp hi]
  | cons a s ha hs ih =>
    obtain ⟨X, e, he, hrange⟩ := ih
    refine ⟨X ⨿ Z, coprod.desc e (σ a), ?_, ?_⟩
    · rw [coprod.desc_comp, hσ]
      infer_instance
    · intro i hi
      rcases Finset.mem_cons.mp hi with rfl | hi
      · rintro _ ⟨z, rfl⟩
        exact ⟨(coprod.inr : Z ⟶ X ⨿ Z) z, by rw [← Scheme.Hom.comp_apply, coprod.inr_desc]⟩
      · rintro _ ⟨z, rfl⟩
        obtain ⟨x, hx⟩ := hrange i hi ⟨z, rfl⟩
        exact ⟨(coprod.inl : X ⟶ X ⨿ Z) x, by rw [← Scheme.Hom.comp_apply, coprod.inl_desc, hx]⟩

/-- A morphism with finitely many sections whose images cover its source is universally
closed. -/
theorem universallyClosed_of_sections {Y Z : Scheme.{u}} (p : Y ⟶ Z) {I : Type*}
    (σ : I → (Z ⟶ Y)) (hσ : ∀ i, σ i ≫ p = 𝟙 Z) (s : Finset I) (hs : s.Nonempty)
    (hcov : ∀ y : Y, ∃ i ∈ s, y ∈ Set.range (σ i)) : UniversallyClosed p := by
  obtain ⟨X, e, he, hrange⟩ := exists_isFinite_cover p σ hσ s hs
  have : Surjective e := ⟨fun y => by
    obtain ⟨i, hi, hy⟩ := hcov y
    exact hrange i hi hy⟩
  have : UniversallyClosed (e ≫ p) := inferInstance
  exact UniversallyClosed.of_comp_surjective e p

end Schemes

section Translation

variable {S : Scheme.{u}} (A : GroupScheme S)

/-- Left multiplication by a section `s` of a group scheme. -/
def leftMul (s : 𝟙_ (Over S) ⟶ A.X) : A.X ⟶ A.X :=
  lift (toUnit A.X ≫ s) (𝟙 A.X) ≫ μ

theorem comp_leftMul (s : 𝟙_ (Over S) ⟶ A.X) {T : Over S} (c : T ⟶ A.X) :
    c ≫ leftMul A s = (toUnit T ≫ s) * c := by
  rw [leftMul, ← Category.assoc, comp_lift, ← Category.assoc, toUnit_unique (c ≫ toUnit A.X),
    Category.comp_id, Hom.mul_def]

/-- Right multiplication by a section `s` of a group scheme. -/
def rightMul (s : 𝟙_ (Over S) ⟶ A.X) : A.X ⟶ A.X :=
  lift (𝟙 A.X) (toUnit A.X ≫ s) ≫ μ

theorem comp_rightMul (s : 𝟙_ (Over S) ⟶ A.X) {T : Over S} (c : T ⟶ A.X) :
    c ≫ rightMul A s = c * (toUnit T ≫ s) := by
  rw [rightMul, ← Category.assoc, comp_lift, ← Category.assoc, toUnit_unique (c ≫ toUnit A.X),
    Category.comp_id, Hom.mul_def]

end Translation

section Cover

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {S H : GroupScheme (Spec (CommRingCat.of k))}

/-- If a subgroup `H` of a group scheme `S` locally of finite type and quasi-compact over an
algebraically closed field has open image, finitely many left translates of `H` by rational
points cover `S`. -/
theorem exists_finset_leftMul_cover [LocallyOfFiniteType S.X.hom] [CompactSpace S.X.left]
    (f : H ⟶ S) (hopen : IsOpen (Set.range f.hom.hom.left)) :
    ∃ t : Finset (𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ S.X),
      ∀ x : S.X.left, ∃ s ∈ t, (leftMul S s⁻¹).left x ∈ Set.range f.hom.hom.left := by
  classical
  let V := Set.range f.hom.hom.left
  let U : (𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ S.X) → Set S.X.left :=
    fun s => (leftMul S s⁻¹).left ⁻¹' V
  have hU : ∀ s, IsOpen (U s) := fun s => hopen.preimage (leftMul S s⁻¹).left.continuous
  have hpt : ∀ s : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ S.X,
      s.left (IsLocalRing.closedPoint k) ∈ U s := by
    intro s
    change (s ≫ leftMul S s⁻¹).left (IsLocalRing.closedPoint k) ∈ V
    rw [comp_leftMul, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, inv_mul_cancel,
      ← MonObj.one_comp (X := 𝟙_ _) f.hom.hom]
    exact ⟨_, rfl⟩
  have hcov : ⋃ s, U s = Set.univ := by
    by_contra hne
    have hC : IsClosed (⋃ s, U s)ᶜ := (isOpen_iUnion hU).isClosed_compl
    obtain ⟨x, hxC, hxcl⟩ :=
      hC.exists_closed_singleton (Set.nonempty_compl.mpr hne)
    let s : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ S.X :=
      Over.homMk (pointOfClosedPoint S.X.hom x hxcl) (by simp)
    apply hxC
    refine Set.mem_iUnion.mpr ⟨s, ?_⟩
    have h1 := hpt s
    convert h1 using 2
    exact (pointOfClosedPoint_apply S.X.hom x hxcl _).symm
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU (by rw [hcov])
  refine ⟨t, fun x => ?_⟩
  obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact ⟨s, hs, hx⟩

end Cover

section Main

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G S H : GroupScheme (Spec (CommRingCat.of k))}

omit [IsAlgClosed k] in
/-- A morphism constant on the cosets `gH` factors through a flat, surjective, quasi-compact
model `q` whose fibers lie in those cosets. -/
theorem exists_factor (iH : H ⟶ G) {O Q : Over (Spec (CommRingCat.of k))} (π : G.X ⟶ O)
    (q : G.X ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X), g ≫ q = h ≫ q →
      g⁻¹ * h ∈ (SubgroupFunctor.range iH).carrier T)
    (hπ : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g⁻¹ * h ∈ (SubgroupFunctor.range iH).carrier T → g ≫ π = h ≫ π) :
    ∃ ρ : Q ⟶ O, q ≫ ρ = π := by
  have key : ∀ {Z : Scheme.{u}} (a b : Z ⟶ G.X.left), a ≫ q.left = b ≫ q.left →
      a ≫ π.left = b ≫ π.left := by
    intro Z a b hab
    let T : Over (Spec (CommRingCat.of k)) := Over.mk (a ≫ G.X.hom)
    have hb : b ≫ G.X.hom = a ≫ G.X.hom := by
      rw [← Over.w q, ← Category.assoc, ← hab, Category.assoc]
    let a' : T ⟶ G.X := Over.homMk a rfl
    let b' : T ⟶ G.X := Over.homMk b hb
    have hq' : a' ≫ q = b' ≫ q := Over.OverMorphism.ext hab
    exact congrArg CommaMorphism.left (hπ T a' b' (hq T a' b' hq'))
  let ρl : Q.left ⟶ O.left := EffectiveEpi.desc q.left π.left key
  have hρ : q.left ≫ ρl = π.left := EffectiveEpi.fac _ _ _
  refine ⟨Over.homMk ρl ?_, Over.OverMorphism.ext hρ⟩
  rw [← cancel_epi q.left, ← Category.assoc, hρ, Over.w π, Over.w q]

/-- Universal closedness of a quotient model `q : G ⟶ Q` by `H`, given a universally closed flat
quotient model `π : G ⟶ O` by `S ⊇ H` with `H` open in `S`. The morphism `Q ⟶ O` through which
`π` factors becomes universally closed after base change along `π`, where finitely many sections
`g ↦ (g, q(g s))` cover `G ×_O Q`; fpqc descent along `π` concludes. -/
theorem universallyClosed_of_isOpen_range (iS : S ⟶ G) (hiS : IsClosedSubgroup iS)
    (iH : H ⟶ G) (f : H ⟶ S) (hiH : IsClosedSubgroup iH) (hf : f ≫ iS = iH)
    (hopen : IsOpen (Set.range f.hom.hom.left))
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    {O : Over (Spec (CommRingCat.of k))} (π : G.X ⟶ O) [UniversallyClosed O.hom]
    [Flat π.left] [Surjective π.left] [QuasiCompact π.left]
    (hπ : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ π = h ≫ π ↔ g⁻¹ * h ∈ (SubgroupFunctor.range iS).carrier T)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range iH).carrier T) :
    UniversallyClosed Q.hom := by
  have hfH : f.hom.hom ≫ iS.hom.hom = iH.hom.hom := by rw [← hf]; rfl
  -- `f` is a closed immersion.
  have : IsClosedImmersion iS.hom.hom.left := hiS
  have : IsClosedImmersion (f.hom.hom.left ≫ iS.hom.hom.left) := by
    rw [← Over.comp_left, hfH]
    exact hiH
  have : IsClosedImmersion f.hom.hom.left := IsClosedImmersion.of_comp _ iS.hom.hom.left
  -- `S` is of finite type and quasi-compact over `k`.
  have hSX : iS.hom.hom.left ≫ G.X.hom = S.X.hom := Over.w iS.hom.hom
  have : LocallyOfFiniteType S.X.hom := by rw [← hSX]; infer_instance
  have : QuasiCompact S.X.hom := by rw [← hSX]; infer_instance
  have : CompactSpace S.X.left := QuasiCompact.compactSpace_of_compactSpace S.X.hom
  -- Points of `H` are points of `S`.
  have hHS : ∀ {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ G.X),
      x ∈ (SubgroupFunctor.range iH).carrier T → x ∈ (SubgroupFunctor.range iS).carrier T := by
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ f.hom.hom, by rw [Category.assoc, hfH]⟩
  -- The comparison morphism `ρ : Q ⟶ O`.
  obtain ⟨ρ, hρ⟩ := exists_factor iH π q (fun T g h e => (hq T g h).mp e)
    (fun T g h e => (hπ T g h).mpr (hHS _ e))
  have hρl : q.left ≫ ρ.left = π.left := congrArg CommaMorphism.left hρ
  -- It suffices to prove universal closedness of the base change of `ρ` along `π`.
  suffices hY : UniversallyClosed (pullback.fst π.left ρ.left) by
    have : UniversallyClosed ρ.left :=
      MorphismProperty.of_pullback_fst_of_descendsAlong (P := @UniversallyClosed)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
        ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hY
    rw [← Over.w ρ]
    infer_instance
  -- Finitely many rational translates of `H` cover `S`.
  obtain ⟨t, ht⟩ := exists_finset_leftMul_cover f hopen
  have htne : t.Nonempty := by
    obtain ⟨s, hs, -⟩ := ht ((η[S.X] : 𝟙_ _ ⟶ S.X).left (IsLocalRing.closedPoint k))
    exact ⟨s, hs⟩
  -- The sections `g ↦ (g, q(g s))` of `G ×_O Q ⟶ G`.
  let sG : (𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ S.X) →
      (𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X) := fun s => s ≫ iS.hom.hom
  have hR : ∀ s, rightMul G (sG s) ≫ π = π := by
    intro s
    have h1 : 𝟙 G.X ≫ π = rightMul G (sG s) ≫ π := by
      refine (hπ G.X (𝟙 G.X) (rightMul G (sG s))).mpr ?_
      rw [← Category.id_comp (rightMul G (sG s)), comp_rightMul, inv_mul_cancel_left]
      exact SubgroupFunctor.mem_range.mpr ⟨toUnit G.X ≫ s, by simp [sG]⟩
    rw [Category.id_comp] at h1
    exact h1.symm
  let σ : (𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ S.X) → (G.X.left ⟶ pullback π.left ρ.left) :=
    fun s => pullback.lift (𝟙 _) ((rightMul G (sG s)).left ≫ q.left) (by
      rw [Category.id_comp, Category.assoc, hρl, ← Over.comp_left, hR])
  have hσ : ∀ s, σ s ≫ pullback.fst π.left ρ.left = 𝟙 _ := fun s => pullback.lift_fst _ _ _
  -- `G ×_O G ⟶ G ×_O Q` is surjective, as a base change of `q`.
  let w2y : pullback π.left π.left ⟶ pullback π.left ρ.left :=
    pullback.map _ _ _ _ (𝟙 _) q.left (𝟙 _) (by simp) (by simp [hρl])
  have e1 : w2y ≫ pullback.fst π.left ρ.left = pullback.fst π.left π.left := by
    simp only [w2y, pullback.map, pullback.lift_fst, Category.comp_id]
  have e2 : w2y ≫ pullback.snd π.left ρ.left = pullback.snd π.left π.left ≫ q.left := by
    simp only [w2y, pullback.map, pullback.lift_snd]
  have hw : IsPullback (pullback.snd π.left π.left) w2y q.left (pullback.snd π.left ρ.left) := by
    refine IsPullback.of_bot (v₂₁ := pullback.fst π.left ρ.left) (v₂₂ := ρ.left)
      (h₃₁ := π.left) ?_ e2.symm (IsPullback.of_hasPullback π.left ρ.left).flip
    rw [e1, hρl]
    exact (IsPullback.of_hasPullback π.left π.left).flip
  have : Surjective w2y := MorphismProperty.of_isPullback (P := @Surjective) hw inferInstance
  -- The sections cover `G ×_O Q`.
  have hcov : ∀ y : ↥(pullback π.left ρ.left), ∃ s ∈ t, y ∈ Set.range (σ s) := by
    intro y
    obtain ⟨w, rfl⟩ := w2y.surjective y
    let tw := (pullback π.left π.left).fromSpecResidueField w
    let a := tw ≫ pullback.fst π.left π.left
    let b := tw ≫ pullback.snd π.left π.left
    have hab : a ≫ π.left = b ≫ π.left := by
      simp only [a, b, Category.assoc, pullback.condition]
    let T : Over (Spec (CommRingCat.of k)) := Over.mk (a ≫ G.X.hom)
    have : Subsingleton T.left :=
      inferInstanceAs (Subsingleton (Spec ((pullback π.left π.left).residueField w)))
    have : IsReduced T.left :=
      inferInstanceAs (IsReduced (Spec ((pullback π.left π.left).residueField w)))
    have hb : b ≫ G.X.hom = a ≫ G.X.hom := by
      rw [← Over.w π, ← Category.assoc, ← hab, Category.assoc]
    let a' : T ⟶ G.X := Over.homMk a rfl
    let b' : T ⟶ G.X := Over.homMk b hb
    have hπab : a' ≫ π = b' ≫ π := Over.OverMorphism.ext hab
    obtain ⟨c, hc⟩ := SubgroupFunctor.mem_range.mp ((hπ T a' b').mp hπab)
    let z0 : T.left := IsLocalRing.closedPoint ((pullback π.left π.left).residueField w)
    obtain ⟨s, hs, hsx⟩ := ht (c.left z0)
    let c' : T ⟶ S.X := c ≫ leftMul S s⁻¹
    have hc' : Set.range c'.left ⊆ Set.range f.hom.hom.left := by
      rintro _ ⟨z, rfl⟩
      rw [Subsingleton.elim z z0]
      obtain ⟨y, hy⟩ := hsx
      exact ⟨y, by rw [hy, Over.comp_left, Scheme.Hom.comp_apply]⟩
    obtain ⟨d0, hd0⟩ := exists_lift_of_range_subset f.hom.hom.left c'.left hc'
    have hd0H : d0 ≫ H.X.hom = T.hom := by
      rw [← Over.w f.hom.hom, ← Category.assoc, hd0, Over.w c']
    let d : T ⟶ H.X := Over.homMk d0 hd0H
    have hd : d ≫ f.hom.hom = c' := Over.OverMorphism.ext hd0
    have hinv : s⁻¹ ≫ iS.hom.hom = (s ≫ iS.hom.hom)⁻¹ := by
      simpa using GrpObj.zpow_comp s (-1) iS.hom.hom
    have hkey : (a' * (toUnit T ≫ sG s))⁻¹ * b' ∈ (SubgroupFunctor.range iH).carrier T := by
      refine SubgroupFunctor.mem_range.mpr ⟨d, ?_⟩
      rw [← hfH, ← Category.assoc, hd]
      change (c ≫ leftMul S s⁻¹) ≫ iS.hom.hom = _
      rw [comp_leftMul, MonObj.mul_comp, hc, Category.assoc, hinv, GrpObj.comp_inv, mul_inv_rev,
        mul_assoc]
    have hqq : (a' * (toUnit T ≫ sG s)) ≫ q = b' ≫ q := (hq T _ _).mpr hkey
    refine ⟨s, hs, a z0, ?_⟩
    have hrel : tw ≫ w2y = a ≫ σ s := by
      apply pullback.hom_ext
      · rw [Category.assoc, e1, Category.assoc, hσ, Category.comp_id]
      · have e4 : a ≫ (rightMul G (sG s)).left = (a' * (toUnit T ≫ sG s)).left := by
          rw [← comp_rightMul]
          rfl
        have e5 := congrArg CommaMorphism.left hqq
        simp only [Over.comp_left] at e5
        rw [Category.assoc, e2, Category.assoc, pullback.lift_snd, ← Category.assoc a, e4, e5,
          ← Category.assoc]
        rfl
    rw [← Scheme.Hom.comp_apply, ← hrel, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  exact universallyClosed_of_sections (pullback.fst π.left ρ.left) σ hσ t htne hcov

end Main

end FiniteIndexTransfer

open FiniteIndexTransfer in
/-- Properness transfer: over an algebraically closed field, a proper flat quotient model of `G`
by a closed subgroup `S` makes every supplied quotient model of `G` by a closed subgroup `H` of `S`
with open image proper. -/
theorem finiteIndexQuotientProperTransfer :
    FiniteIndexQuotientProperTransferStatement.{u} := by
  intro k _ _ G _ _ S iS hiS H iH f hiH hf hopen O π hO hπf hπs hπq hπ Q q hQs hQl hQq hqs
    hqsurj hqq hq
  have : UniversallyClosed O.hom := hO.toUniversallyClosed
  have : UniversallyClosed Q.hom :=
    universallyClosed_of_isOpen_range iS hiS iH f hiH hf hopen π hπ q hq
  exact { toIsSeparated := hQs, toUniversallyClosed := this, toLocallyOfFiniteType := hQl }

end Langlands.GroupScheme
