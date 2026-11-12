import Langlands.AlgebraicGeometry.LangWeil.SpaceFamily.FieldPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartFibreCount
import Langlands.AlgebraicGeometry.AlgebraicSpace.FinitePresentationChartSquares
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability
import Langlands.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeSourceDescentProof
import Langlands.Global.AdelicSpaceLevelPointsStatement
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Uniform finite-field charts of a quasi-separated algebraic space of finite type over ℤ

Let `B` be a quasi-separated algebraic space of finite type over `ℤ`. There are finitely many
affine schemes `M_i` of finite type over `ℤ` with étale maps `h_{M_i} → B` such that, for every
finite field `κ`, every `κ`-point of `B` comes from a `κ`-point of one of the `M_i`.

For one point this is `FieldPointEtaleLift.exists_affine_etale_point`. Here the construction
is made uniform. A `κ`-point `x` of `B` is the image of a point `ℓ` of an affine piece `V` of
an atlas with values in a finite extension `L` of `κ`. The Galois group of `L/κ` is cyclic,
of order `r ≤ D`, where `D` bounds the fibres of the étale chart `V → B`
(`EtaleChartFibreCount.exists_fibre_card_le`). The cyclic group `G = ℤ/r` acts on the
`G`-indexed fibre power `V ×_B ⋯ ×_B V` by translating the index, freely on the stable open
where the coordinates are pairwise distinct. That open is a Noetherian scheme, so it is covered
by finitely many affine opens, and each of them gives a `G`-stable affine open with an affine
quotient that maps étale to `B`. These quotients, for all affine pieces `V` and all `r ≤ D`,
are the charts. The point with coordinates the Galois conjugates of `ℓ` is fixed by `G`, so
it gives a Galois-invariant `L`-point of one quotient, which descends to `κ`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.LangWeil.SpaceFamily

open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace FiniteFieldCharts

section Quotient

open OverAction

variable {S : Scheme.{u}} {G : Type u} [Group G] [Finite G] {Z : Over S}

/-- `OverAction.exists_quotient_chart`, with the quotient locally of finite type over the
base when `Z` is: the quotient map is finite étale surjective. -/
theorem exists_quotient_chart_lft (τ : OverAction G Z) (U : Z.left.Opens)
    (hU : ∀ g, (τ.act g).left ⁻¹ᵁ U = U) (hfree : τ.IsFree) (X : AlgebraicSpace S)
    [IsAffine (resOver U).left] [LocallyOfFiniteType Z.hom]
    (t : (schemeYoneda S).obj Z ⟶ X.presheaf) (ht : IsEtale t)
    (hinv : ∀ g, (schemeYoneda S).map (τ.act g) ≫ t = t) :
    ∃ (M : Over S) (q : resOver U ⟶ M) (tM : (schemeYoneda S).obj M ⟶ X.presheaf),
      IsAffine M.left ∧ IsEtale tM ∧ LocallyOfFiniteType M.hom ∧
        (∀ g, τ.resAct U hU g ≫ q.left = q.left) ∧
        (schemeYoneda S).map q ≫ tM = (schemeYoneda S).map (resOverι U) ≫ t := by
  have hinvA : ∀ g, (schemeYoneda S).map
      (FiniteActionChart.actOver (τ.restrict U hU hfree) (τ.restrict_over U hU hfree) g) ≫
        (schemeYoneda S).map (resOverι U) ≫ t = (schemeYoneda S).map (resOverι U) ≫ t := by
    intro g
    rw [← Functor.map_comp_assoc, τ.actOver_resOverι U hU hfree g, Functor.map_comp_assoc,
      hinv]
  obtain ⟨tM, htM⟩ := FiniteActionChart.exists_desc (A := resOver U) (τ.restrict U hU hfree)
    (τ.restrict_over U hU hfree) (τ.restrict U hU hfree).quotient X.toSheaf
    ((schemeYoneda S).map (resOverι U) ≫ t) hinvA
  let q := FiniteActionChart.quotientMapOver (τ.restrict U hU hfree)
    (τ.restrict_over U hU hfree) (τ.restrict U hU hfree).quotient
  have hlft : LocallyOfFiniteType (q.left ≫ (FiniteActionChart.quotientOver
      (τ.restrict U hU hfree) (τ.restrict_over U hU hfree)
      (τ.restrict U hU hfree).quotient).hom) := by
    rw [Over.w q]
    change LocallyOfFiniteType (U.ι ≫ Z.hom)
    infer_instance
  refine ⟨_, q, tM, inferInstance, ?_,
    locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp _ _ _ _ _
      inferInstance inferInstance inferInstance hlft,
    fun g => (τ.restrict U hU hfree).quotient.invariant g, htM⟩
  apply isEtale_of_finiteEtale_comp X.hasRepresentableDiagonal q
  rw [htM]
  exact IsEtale.comp (isEtale_map _ (inferInstanceAs (Etale U.ι))) ht

end Quotient

section Sheaf

variable {S : Scheme.{u}}

/-- Maps from a scheme to an algebraic space that agree after composing with an fppf cover of
the scheme agree. -/
theorem eq_of_comp_eq (X : AlgebraicSpace S) {A M : Over S} (q : A ⟶ M) [Flat q.left]
    [LocallyOfFinitePresentation q.left] [Surjective q.left]
    {x₁ x₂ : (schemeYoneda S).obj M ⟶ X.presheaf}
    (h : (schemeYoneda S).map q ≫ x₁ = (schemeYoneda S).map q ≫ x₂) : x₁ = x₂ := by
  let q' : (schemeSheaf S).obj A ⟶ (schemeSheaf S).obj M := (schemeSheaf S).map q
  have : Sheaf.IsLocallySurjective q' := isLocallySurjective_schemeYoneda_map q
  have : Epi q' := inferInstance
  let y₁ : (schemeSheaf S).obj M ⟶ X.toSheaf := ObjectProperty.homMk x₁
  let y₂ : (schemeSheaf S).obj M ⟶ X.toSheaf := ObjectProperty.homMk x₂
  have hy : q' ≫ y₁ = q' ≫ y₂ := ObjectProperty.hom_ext _ h
  exact congrArg (fun f => f.hom) ((cancel_epi q').1 hy)

end Sheaf

section FibrePower

variable {S : Scheme.{u}} [IsAffine S] {X : AlgebraicSpace S} {V : Over S} [IsAffine V.left]
  {a : (schemeYoneda S).obj V ⟶ X.presheaf}

/-- Adding a factor to a compact fibre power of an affine chart of a quasi-separated space
keeps it compact: the new fibre power maps quasi-compactly to `V ×_S P`. -/
theorem compactSpace_succ (hX : IsQuasiSeparated X)
    (ha : (schemeYoneda S).relativelyRepresentable a) {n : ℕ}
    (P : ChartFibrePower a (Fin (n + 1))) [CompactSpace P.obj.left] :
    CompactSpace (ChartFibrePower.succ ha P).obj.left := by
  have : CompactSpace ↥(Limits.pullback V.hom P.obj.hom : Scheme.{u}) := inferInstance
  have hc : CompactSpace (V ⨯ P.obj).left :=
    (Over.prodLeftIsoPullback V P.obj).inv.homeomorph.compactSpace
  have hqc := relative_diagonal_property_chart_pairing @QuasiCompact hX _ _ a P.toBase
    (ChartFibrePower.succ_isPullback ha P)
  exact @QuasiCompact.compactSpace_of_compactSpace _ _ _ hqc hc

theorem compactSpace_fin (hX : IsQuasiSeparated X)
    (ha : (schemeYoneda S).relativelyRepresentable a) :
    ∀ n : ℕ, CompactSpace (ChartFibrePower.fin ha n).obj.left
  | 0 => inferInstanceAs (CompactSpace V.left)
  | n + 1 => by
    have := compactSpace_fin hX ha n
    exact compactSpace_succ hX ha (ChartFibrePower.fin ha n)

/-- A finite nonempty fibre power of an étale affine chart of a quasi-separated space is
separated with étale projections, and compact. -/
theorem exists_compact_fibrePower (hX : IsQuasiSeparated X) (ha : IsEtale a) (ι : Type u)
    [Finite ι] [Nonempty ι] :
    ∃ P : ChartFibrePower a ι, _root_.AlgebraicGeometry.IsSeparated P.obj.hom ∧
      (∀ i, Etale (P.pr i).left) ∧ CompactSpace P.obj.left := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain _ | n := n
  · exact (IsEmpty.false (e (Classical.arbitrary ι))).elim
  obtain ⟨h₁, h₂⟩ := ChartFibrePower.fin_properties ha n
  exact ⟨(ChartFibrePower.fin ha.1 n).reindex e, h₁, fun i => h₂ (e i),
    compactSpace_fin hX ha.1 n⟩

end FibrePower

section Uniform

open OverAction

/-- A compact scheme is covered by finitely many affine opens. -/
theorem exists_finset_affineOpens_cover (Z : Scheme.{u}) [CompactSpace Z] :
    ∃ s : Finset Z.affineOpens, ∀ x : Z, ∃ W ∈ s, x ∈ (W : Z.Opens) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun W : Z.affineOpens => ((W : Z.Opens) : Set Z))
    (fun W => W.1.isOpen) (fun x _ => by
      obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ (⊤ : Z.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨W, hW⟩, hx⟩)
  refine ⟨s, fun x => ?_⟩
  have hx := hs (Set.mem_univ x)
  simp only [Set.mem_iUnion] at hx
  obtain ⟨W, hW, hx⟩ := hx
  exact ⟨W, hW, hx⟩

variable {S : Scheme.{u}} {G : Type u} [Group G]

/-- An equivariant point of a scheme with an action, from a one-point scheme and landing in a
stable open, factors through the open, and its composite with an invariant map from the open
is invariant. -/
theorem exists_invariant_point {Z : Over S} (τ : OverAction G Z) (U : Z.left.Opens)
    (hU : ∀ g, (τ.act g).left ⁻¹ᵁ U = U) {M : Over S} (q : resOver U ⟶ M)
    (hq : ∀ g, τ.resAct U hU g ≫ q.left = q.left) {Λ : Over S} [Subsingleton Λ.left]
    (σ : OverAction G Λ) (z : Λ ⟶ Z) (hz : ∀ g, z ≫ τ.act g = σ.act g ≫ z) (y : Λ.left)
    (hy : z.left y ∈ U) :
    ∃ z' : Λ ⟶ resOver U, z' ≫ resOverι U = z ∧ ∀ g, σ.act g ≫ z' ≫ q = z' ≫ q := by
  have hzg : ∀ g, z.left ≫ (τ.act g).left = (σ.act g).left ≫ z.left := fun g =>
    congrArg CommaMorphism.left (hz g)
  have hrange : Set.range z.left ⊆ Set.range (resOverι U).left := by
    rintro _ ⟨y', rfl⟩
    rw [Subsingleton.elim y' y]
    exact ⟨⟨z.left y, hy⟩, Scheme.Opens.ι_apply _ _⟩
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : Λ.left ⟶ (resOver U).left, z₁ ≫ (resOverι U).left = z.left :=
    ⟨_root_.AlgebraicGeometry.IsOpenImmersion.lift (resOverι U).left z.left hrange,
      _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hrange⟩
  let z' : Λ ⟶ resOver U := Over.homMk z₁ (by
    change z₁ ≫ (resOverι U).left ≫ Z.hom = Λ.hom
    rw [reassoc_of% hz₁, Over.w z])
  refine ⟨z', Over.OverMorphism.ext hz₁, fun g => ?_⟩
  have h₁ : (σ.act g).left ≫ z₁ = z₁ ≫ τ.resAct U hU g := by
    rw [← cancel_mono (resOverι U).left, Category.assoc, hz₁, Category.assoc,
      OverAction.resAct_ι, reassoc_of% hz₁, hzg]
  apply Over.OverMorphism.ext
  change (σ.act g).left ≫ z₁ ≫ q.left = z₁ ≫ q.left
  rw [reassoc_of% h₁, hq]

variable [Finite G]

/-- **Uniform quotient charts.** Let a finite group act freely on a compact separated scheme
`Z` locally of finite type over `S`, and let `t : h_Z → X` be an invariant étale map. There
are finitely many affine schemes `M_i` locally of finite type over `S` with étale maps
`h_{M_i} → X` such that every equivariant point of `Z` with values in a one-point scheme
gives an invariant point of some `M_i` with the same image in `X`. -/
theorem exists_uniform_charts (X : AlgebraicSpace S) {Z : Over S} (τ : OverAction G Z)
    (hfree : τ.IsFree) [Z.left.IsSeparated] [CompactSpace Z.left] [LocallyOfFiniteType Z.hom]
    (t : (schemeYoneda S).obj Z ⟶ X.presheaf) (ht : IsEtale t)
    (hinv : ∀ g, (schemeYoneda S).map (τ.act g) ≫ t = t) :
    ∃ (n : ℕ) (M : Fin n → Over S) (tM : ∀ i, (schemeYoneda S).obj (M i) ⟶ X.presheaf),
      (∀ i, IsAffine (M i).left) ∧ (∀ i, IsEtale (tM i)) ∧
        (∀ i, LocallyOfFiniteType (M i).hom) ∧
        ∀ (Λ : Over S) [Nonempty Λ.left] [Subsingleton Λ.left] (σ : OverAction G Λ)
          (z : Λ ⟶ Z), (∀ g, z ≫ τ.act g = σ.act g ≫ z) →
          ∃ i, ∃ w : Λ ⟶ M i, (∀ g, σ.act g ≫ w = w) ∧
            (schemeYoneda S).map w ≫ tM i = (schemeYoneda S).map z ≫ t := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_affineOpens_cover Z.left
  have hA : ∀ W : s, IsAffine (resOver (τ.orbitInf (W.1 : Z.left.Opens))).left :=
    fun W => τ.isAffineOpen_orbitInf W.1.2
  choose M q tM hM htM hlft hq hqt using fun W : s =>
    @exists_quotient_chart_lft S G _ _ Z τ (τ.orbitInf (W.1 : Z.left.Opens))
      (τ.preimage_orbitInf _) hfree X (hA W) _ t ht hinv
  let e := s.equivFin
  refine ⟨s.card, fun i => M (e.symm i), fun i => tM (e.symm i), fun i => hM _,
    fun i => htM _, fun i => hlft _, ?_⟩
  intro Λ _ _ σ z hz
  obtain ⟨y⟩ := ‹Nonempty Λ.left›
  obtain ⟨W, hWs, hyW⟩ := hs (z.left y)
  obtain ⟨j, hj⟩ := e.symm.surjective ⟨W, hWs⟩
  have hzg : ∀ g, z.left ≫ (τ.act g).left = (σ.act g).left ≫ z.left := fun g =>
    congrArg CommaMorphism.left (hz g)
  have hp : ∀ g, (τ.act g).left (z.left y) = z.left y := by
    intro g
    rw [← Scheme.Hom.comp_apply, hzg, Scheme.Hom.comp_apply,
      Subsingleton.elim ((σ.act g).left y) y]
  have hyU : z.left y ∈ τ.orbitInf (W : Z.left.Opens) :=
    τ.mem_orbitInf.2 fun g => by rw [hp]; exact hyW
  have hyU' : z.left y ∈ τ.orbitInf ((e.symm j).1 : Z.left.Opens) := by rw [hj]; exact hyU
  obtain ⟨z', hz', hw⟩ := exists_invariant_point τ _ (τ.preimage_orbitInf _) (q (e.symm j))
    (hq (e.symm j)) σ z hz y hyU'
  refine ⟨j, z' ≫ q (e.symm j), hw, ?_⟩
  rw [Functor.map_comp_assoc, hqt, ← Functor.map_comp_assoc, hz']

/-- **Charts for orbits of points.** Let `X` be a quasi-separated algebraic space over an
affine locally Noetherian scheme `S`, `a : h_V → X` an étale map from an affine scheme `V`
locally of finite type over `S`, and `G` a finite group. There are finitely many affine
schemes `M_i` locally of finite type over `S` with étale maps `h_{M_i} → X` with the
following property. Let `Λ` be a one-point scheme over `S` with a `G`-action `σ`, and let
`v : G → (Λ → V)` be an injective family of points with the same image in `X`, equivariant
in the sense `σ_g ∘ v_e = v_{g e}`. Then the image of `v_1` in `X` is the image of a
`σ`-invariant point of some `M_i`. -/
theorem exists_orbit_charts [IsAffine S] [IsLocallyNoetherian S] {X : AlgebraicSpace S}
    (hX : IsQuasiSeparated X) {V : Over S} [IsAffine V.left] [LocallyOfFiniteType V.hom]
    {a : (schemeYoneda S).obj V ⟶ X.presheaf} (ha : IsEtale a) (G : Type u) [Group G]
    [Finite G] :
    ∃ (n : ℕ) (M : Fin n → Over S) (tM : ∀ i, (schemeYoneda S).obj (M i) ⟶ X.presheaf),
      (∀ i, IsAffine (M i).left) ∧ (∀ i, IsEtale (tM i)) ∧
        (∀ i, LocallyOfFiniteType (M i).hom) ∧
        ∀ (Λ : Over S) [Nonempty Λ.left] [Subsingleton Λ.left] (σ : OverAction G Λ)
          (v : G → (Λ ⟶ V)), Function.Injective v → (∀ g e, σ.act g ≫ v e = v (g * e)) →
          (∀ e, (schemeYoneda S).map (v e) ≫ a = (schemeYoneda S).map (v 1) ≫ a) →
          ∃ i, ∃ w : Λ ⟶ M i, (∀ g, σ.act g ≫ w = w) ∧
            (schemeYoneda S).map w ≫ tM i = (schemeYoneda S).map (v 1) ≫ a := by
  obtain ⟨Y, hYsep, hYet, hYc⟩ := exists_compact_fibrePower hX ha G
  obtain ⟨ρ, hρ⟩ : ∃ ρ : OverAction G Y.obj, ∀ g e, ρ.act g ≫ Y.pr e = Y.pr (g * e) :=
    ⟨⟨Y.act, Y.act_one, Y.act_mul⟩, Y.act_pr⟩
  -- the stable open where the coordinates are pairwise distinct; the action is free there
  obtain ⟨W, hW, hWD, hWmem⟩ : ∃ W : Y.obj.left.Opens, (∀ g, (ρ.act g).left ⁻¹ᵁ W = W) ∧
      (∀ s ∈ W, s ∈ FieldPointEtaleLift.distinctLocus Y) ∧
        ∀ s, (∀ g, (ρ.act g).left s ∈ FieldPointEtaleLift.distinctLocus Y) → s ∈ W := by
    refine ⟨ρ.orbitInf (FieldPointEtaleLift.distinctLocus Y), ρ.preimage_orbitInf _,
      fun s hs => ?_, fun s hs => ρ.mem_orbitInf.2 hs⟩
    have h := ρ.mem_orbitInf.1 hs 1
    rw [ρ.one, Over.id_left] at h
    exact h
  obtain ⟨τ, hτ⟩ : ∃ τ : OverAction G (resOver W),
      ∀ g, τ.act g ≫ resOverι W = resOverι W ≫ ρ.act g :=
    ⟨FieldPointEtaleLift.resAction ρ W hW, FieldPointEtaleLift.resAction_ι ρ W hW⟩
  have hfree : τ.IsFree := by
    intro Tq _ b g h hgh
    by_contra hne
    have hgh' : b ≫ (τ.act g).left = b ≫ (τ.act h).left := hgh
    let c : Tq ⟶ Y.obj.left := b ≫ (resOverι W).left
    have hc : ∀ γ, b ≫ (τ.act γ).left ≫ (resOverι W).left = c ≫ (ρ.act γ).left := fun γ => by
      rw [← Over.comp_left, hτ, Over.comp_left, ← Category.assoc]
    have hcgh : c ≫ (ρ.act g).left = c ≫ (ρ.act h).left := by
      rw [← hc, ← hc, reassoc_of% hgh']
    let T' : Over S := Over.mk (c ≫ Y.obj.hom)
    have : Nonempty T'.left := ‹Nonempty Tq›
    let b' : T' ⟶ Y.obj := Over.homMk c rfl
    have hb' : ∀ t, b'.left t ∈ FieldPointEtaleLift.distinctLocus Y := fun t => hWD _ (by
      change (b ≫ (resOverι W).left) t ∈ W
      rw [Scheme.Hom.comp_apply]
      exact (b t).2)
    have hne' : g * 1 ≠ h * 1 := by simpa using hne
    apply FieldPointEtaleLift.ne_of_mem_distinctLocus Y b' hb' hne'
    have hb'gh : b' ≫ ρ.act g = b' ≫ ρ.act h := Over.OverMorphism.ext hcgh
    rw [← hρ, ← hρ, reassoc_of% hb'gh]
  have : _root_.AlgebraicGeometry.IsSeparated Y.obj.hom := hYsep
  have : _root_.AlgebraicGeometry.IsSeparated (resOver W).hom := by
    change _root_.AlgebraicGeometry.IsSeparated (W.ι ≫ Y.obj.hom)
    infer_instance
  have : (resOver W).left.IsSeparated :=
    ⟨by rw [← terminal.comp_from (resOver W).hom]; infer_instance⟩
  have : LocallyOfFiniteType Y.obj.hom := by
    rw [← Over.w (Y.pr 1)]
    have := hYet 1
    infer_instance
  have : LocallyOfFiniteType (resOver W).hom := by
    change LocallyOfFiniteType (W.ι ≫ Y.obj.hom)
    infer_instance
  have : IsLocallyNoetherian Y.obj.left := LocallyOfFiniteType.isLocallyNoetherian Y.obj.hom
  have : AlgebraicGeometry.IsNoetherian Y.obj.left := AlgebraicGeometry.IsNoetherian.mk
  have : CompactSpace (resOver W).left :=
    isCompact_iff_compactSpace.1
      (TopologicalSpace.NoetherianSpace.isCompact (W : Set Y.obj.left))
  -- the invariant étale map from the stable open
  obtain ⟨t, rfl⟩ : ∃ t : (schemeYoneda S).obj (resOver W) ⟶ X.presheaf,
      t = (schemeYoneda S).map (resOverι W ≫ Y.pr 1) ≫ a := ⟨_, rfl⟩
  have ht : IsEtale ((schemeYoneda S).map (resOverι W ≫ Y.pr 1) ≫ a) := by
    refine IsEtale.comp (isEtale_map _ ?_) ha
    have := hYet 1
    rw [Over.comp_left]
    infer_instance
  have hinv : ∀ g, (schemeYoneda S).map (τ.act g) ≫
      (schemeYoneda S).map (resOverι W ≫ Y.pr 1) ≫ a =
        (schemeYoneda S).map (resOverι W ≫ Y.pr 1) ≫ a := by
    intro g
    rw [← Functor.map_comp_assoc, ← Category.assoc, hτ, Category.assoc, hρ,
      Functor.map_comp_assoc, Functor.map_comp_assoc, Y.w (g * 1) 1]
  obtain ⟨n, M, tM, hM, htM, hlft, hpt⟩ := exists_uniform_charts X τ hfree _ ht hinv
  refine ⟨n, M, tM, hM, htM, hlft, ?_⟩
  intro Λ _ _ σ v hv hσv hva
  -- the point of the fibre power with coordinates `v`
  obtain ⟨y, hy⟩ : ∃ y : Λ ⟶ Y.obj, ∀ e, y ≫ Y.pr e = v e :=
    ⟨Y.lift v fun e e' => by rw [hva e, hva e'], Y.lift_pr _ _⟩
  have hyeq : ∀ g, y ≫ ρ.act g = σ.act g ≫ y := by
    intro g
    refine Y.hom_ext _ _ fun e => ?_
    rw [Category.assoc, hρ, hy, Category.assoc, hy, hσv]
  have hyW : ∀ s, y.left s ∈ W := by
    intro s
    refine hWmem _ fun g => ?_
    have hb : ∀ e e', e ≠ e' → (y ≫ ρ.act g) ≫ Y.pr e ≠ (y ≫ ρ.act g) ≫ Y.pr e' := by
      intro e e' hee' h
      rw [Category.assoc, hρ, hy, Category.assoc, hρ, hy] at h
      exact hee' (mul_left_cancel (hv h))
    have := FieldPointEtaleLift.mem_distinctLocus_of_ne Y ha (y ≫ ρ.act g) hb s
    rwa [Over.comp_left, Scheme.Hom.comp_apply] at this
  have hrangeW : Set.range y.left ⊆ Set.range (resOverι W).left := by
    rintro _ ⟨s, rfl⟩
    exact ⟨⟨y.left s, hyW s⟩, Scheme.Opens.ι_apply _ _⟩
  obtain ⟨z, hz⟩ : ∃ z : Λ ⟶ resOver W, z ≫ resOverι W = y := by
    let z₁ := _root_.AlgebraicGeometry.IsOpenImmersion.lift (resOverι W).left y.left hrangeW
    have hz₁ : z₁ ≫ (resOverι W).left = y.left :=
      _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hrangeW
    refine ⟨Over.homMk z₁ ?_, Over.OverMorphism.ext hz₁⟩
    change z₁ ≫ (resOverι W).left ≫ Y.obj.hom = Λ.hom
    rw [reassoc_of% hz₁, Over.w y]
  have hzeq : ∀ g, z ≫ τ.act g = σ.act g ≫ z := by
    intro g
    have h : (z ≫ τ.act g) ≫ resOverι W = (σ.act g ≫ z) ≫ resOverι W := by
      rw [Category.assoc, hτ, ← Category.assoc, hz, Category.assoc, hz, hyeq]
    have h' := congrArg CommaMorphism.left h
    simp only [Over.comp_left] at h'
    apply Over.OverMorphism.ext
    simp only [Over.comp_left]
    rw [← cancel_mono (resOverι W).left]
    simpa only [Category.assoc] using h'
  obtain ⟨i, w, hw, hwt⟩ := hpt Λ σ z hzeq
  refine ⟨i, w, hw, ?_⟩
  rw [hwt, ← Functor.map_comp_assoc, ← Category.assoc, hz, hy]

end Uniform

section Points

open OverAction

/-- A morphism from a one-point scheme whose point lands in an open factors through the
open. -/
theorem exists_factor_resOver {S : Scheme.{u}} {Z Λ : Over S} [Subsingleton Λ.left]
    (U : Z.left.Opens) (z : Λ ⟶ Z) (y : Λ.left) (hy : z.left y ∈ U) :
    ∃ z' : Λ ⟶ resOver U, z' ≫ resOverι U = z := by
  have hrange : Set.range z.left ⊆ Set.range (resOverι U).left := by
    rintro _ ⟨y', rfl⟩
    rw [Subsingleton.elim y' y]
    exact ⟨⟨z.left y, hy⟩, Scheme.Opens.ι_apply _ _⟩
  let z₁ := _root_.AlgebraicGeometry.IsOpenImmersion.lift (resOverι U).left z.left hrange
  have hz₁ : z₁ ≫ (resOverι U).left = z.left :=
    _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hrange
  refine ⟨Over.homMk z₁ ?_, Over.OverMorphism.ext hz₁⟩
  change z₁ ≫ (resOverι U).left ≫ Z.hom = Λ.hom
  rw [reassoc_of% hz₁, Over.w z]

/-- A group acting on a field `L` by automorphisms over `κ` acts on `Spec L` over the
terminal base. -/
def specAction {G : Type u} [Group G] {κ L : Type u} [Field κ] [Field L] [Algebra κ L]
    (ψ : G →* (L ≃ₐ[κ] L)) : OverAction G (toOver (Spec (CommRingCat.of L))) where
  act g := toOverHom (Spec.map (CommRingCat.ofHom ((ψ g : L ≃ₐ[κ] L) : L →+* L)))
  one := by
    rw [← toOverHom_id, ← Spec.map_id]
    congr 2
    ext a
    simp
  mul g h := by
    rw [← toOverHom_comp, ← Spec.map_comp]
    congr 2
    ext a
    simp [map_mul, AlgEquiv.mul_apply]

/-- `EtaleChartFibreCount.exists_fibre_card_le` over the terminal base, for points with
values in fields: the fibres of an étale affine chart of a quasi-separated space are
uniformly bounded. -/
theorem exists_fibre_card_le {X : AlgebraicSpace S0.{u}} (hX : IsQuasiSeparated X)
    {V : Over S0.{u}} [IsAffine V.left] {a : (schemeYoneda S0).obj V ⟶ X.presheaf}
    (ha : IsEtale a) :
    ∃ D : ℕ, ∀ (L : Type u) [Field L] (ι : Type u) [Finite ι]
      (v : ι → (toOver (Spec (CommRingCat.of L)) ⟶ V)), Function.Injective v →
      (∀ i j, (schemeYoneda S0).map (v i) ≫ a = (schemeYoneda S0).map (v j) ≫ a) →
        Nat.card ι ≤ D := by
  obtain ⟨D, hD⟩ := EtaleChartFibreCount.exists_fibre_card_le (C := ULift.{u} ℤ) a hX ha
  refine ⟨D, fun L _ ι _ v hv hva => ?_⟩
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · simp
  have := Fintype.ofFinite ι
  let : Algebra (ULift.{u} ℤ) L :=
    ((Int.castRingHom L).comp ULift.ringEquiv.toRingHom).toAlgebra
  let c : Langlands.AlgebraicGeometry.PointTopology.ringTest (ULift.{u} ℤ) L ⟶
      toOver (Spec (CommRingCat.of L)) :=
    Over.homMk (𝟙 _) (specULiftZIsTerminal.hom_ext _ _)
  have hc : ∀ i j, c ≫ v i = c ≫ v j → v i = v j := fun i j h => by
    apply Over.OverMorphism.ext
    have h' : 𝟙 _ ≫ (v i).left = 𝟙 _ ≫ (v j).left := congrArg CommaMorphism.left h
    simpa using h'
  rw [Nat.card_eq_fintype_card]
  refine hD L (c ≫ v i₀) ι (fun i => c ≫ v i) (fun i j h => hv (hc i j h)) fun i => ?_
  rw [Functor.map_comp_assoc, Functor.map_comp_assoc, hva i i₀]

/-- **Points with values in a field come from separable points of an atlas.** Let
`a : h_U → X` be a surjective étale map from a scheme. For every `κ`-point `x` of `X`
there are a finite separable extension `L` of `κ` and an `L`-point `ℓ` of `U` with image
the restriction of `x` to `L`, whose conjugates under the automorphisms of `L/κ` are
pairwise distinct. -/
theorem exists_separable_point (X : AlgebraicSpace S0.{u}) {U : Over S0.{u}}
    {a : (schemeYoneda S0).obj U ⟶ X.presheaf} (ha : IsEtale a) (hs : IsSurjective a)
    (κ : Type u) [Field κ]
    (x : (schemeYoneda S0).obj (toOver (Spec (CommRingCat.of κ))) ⟶ X.presheaf) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra κ L), FiniteDimensional κ L ∧
      ∃ ℓ : toOver (Spec (CommRingCat.of L)) ⟶ U,
        Function.Injective (fun γ : L ≃ₐ[κ] L =>
          toOverHom (Spec.map (CommRingCat.ofHom (γ : L →+* L))) ≫ ℓ) ∧
        (schemeYoneda S0).map ℓ ≫ a =
          (schemeYoneda S0).map (toOverHom (specMap κ L)) ≫ x := by
  let P := ha.1.pullback x
  let p : P ⟶ toOver (Spec (CommRingCat.of κ)) := ha.1.snd x
  let q : P ⟶ U := Functor.relativelyRepresentable.fst' ha.1 x
  have hsq : IsPullback ((schemeYoneda _).map q) ((schemeYoneda _).map p) a x :=
    Functor.relativelyRepresentable.isPullback' ha.1 x
  have hpe : Etale p.left := ha.projection x _ p hsq
  have hps : Surjective p.left := hs.projection x _ p hsq
  let T : Over (Spec (CommRingCat.of κ)) := Over.mk p.left
  have : Etale T.hom := hpe
  have : Nonempty T.left := by
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of κ)) := inferInstance
    obtain ⟨z, -⟩ := hps.surj y
    exact ⟨z⟩
  obtain ⟨L, _, _, hL, -, w₀, hw₀⟩ := FieldPointEtaleLift.exists_separable_point_mono T
  let w₀l : Spec (CommRingCat.of L) ⟶ P.left := w₀.left
  have hw₀p : w₀l ≫ p.left = specMap κ L := Over.w w₀
  have : Mono w₀l := hw₀
  let w₁ : toOver (Spec (CommRingCat.of L)) ⟶ P :=
    Over.homMk w₀l (specULiftZIsTerminal.hom_ext _ _)
  have hw₁p : w₁ ≫ p = toOverHom (specMap κ L) := Over.OverMorphism.ext hw₀p
  have hγp : ∀ γ : L ≃ₐ[κ] L,
      (toOverHom (Spec.map (CommRingCat.ofHom (γ : L →+* L))) ≫ w₁) ≫ p =
        toOverHom (specMap κ L) := fun γ => by
    rw [Category.assoc, hw₁p, ← toOverHom_comp, specMap_aut_comp]
  refine ⟨L, inferInstance, inferInstance, hL, w₁ ≫ q, fun γ γ' h => ?_, ?_⟩
  · have hq : (toOverHom (Spec.map (CommRingCat.ofHom (γ : L →+* L))) ≫ w₁) ≫ q =
        (toOverHom (Spec.map (CommRingCat.ofHom (γ' : L →+* L))) ≫ w₁) ≫ q := by
      simpa only [Category.assoc] using h
    have hw := Functor.relativelyRepresentable.hom_ext' ha.1 hq (by rw [hγp, hγp])
    have h1 : Spec.map (CommRingCat.ofHom (γ : L →+* L)) ≫ w₀l =
        Spec.map (CommRingCat.ofHom (γ' : L →+* L)) ≫ w₀l := congrArg CommaMorphism.left hw
    rw [cancel_mono] at h1
    have h2 := Spec.map_injective h1
    ext y
    exact congrArg (fun φ => φ.hom y) h2
  · rw [Functor.map_comp_assoc, hsq.w, ← Functor.map_comp_assoc, hw₁p]

end Points

section Cyclic

/-- The cyclic group of order `r`, in the universe of the schemes. -/
abbrev CyclicGroup (r : ℕ) : Type u := ULift.{u} (Multiplicative (ZMod r))

instance (r : ℕ) : IsCyclic (CyclicGroup.{u} r) :=
  isCyclic_of_surjective (MulEquiv.ulift.symm : Multiplicative (ZMod r) ≃* CyclicGroup.{u} r)
    MulEquiv.ulift.symm.surjective

theorem card_cyclicGroup (r : ℕ) : Nat.card (CyclicGroup.{u} r) = r := by
  rw [Nat.card_ulift, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

end Cyclic

section Main

open OverAction

/-- **Uniform finite-field charts.** Let `B` be a quasi-separated algebraic space of finite
type over `ℤ`. There are finitely many affine schemes `M_i` of finite type over `ℤ` with
étale maps `h_{M_i} → B` such that every point of `B` with values in a finite field is the
image of a point of some `M_i` with values in the same field. -/
theorem exists_finiteField_charts (B : AlgebraicSpace S0.{u}) (hB : IsQuasiSeparated B)
    (hft : FiniteTypeOverRing (ULift.{u} ℤ) B) :
    ∃ (n : ℕ) (M : Fin n → Scheme.{u})
      (t : ∀ i, (schemeYoneda S0).obj (toOver (M i)) ⟶ B.presheaf),
      (∀ i, IsAffine (M i)) ∧ (∀ i, LocallyOfFiniteType (specULiftZIsTerminal.from (M i))) ∧
      (∀ i, IsEtale (t i)) ∧
      ∀ (κ : Type u) [Field κ] [Finite κ]
        (x : (schemeYoneda S0).obj (toOver (Spec (CommRingCat.of κ))) ⟶ B.presheaf),
        ∃ i, ∃ m : Spec (CommRingCat.of κ) ⟶ M i,
          (schemeYoneda S0).map (toOverHom m) ≫ t i = x := by
  classical
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  obtain ⟨U₀, a₀, ha₀, hs₀, hU₀l, hU₀c⟩ := hft
  have : LocallyOfFiniteType U₀.hom := hU₀l
  have : QuasiCompact U₀.hom := hU₀c
  have : CompactSpace U₀.left := QuasiCompact.compactSpace_of_compactSpace U₀.hom
  obtain ⟨s, hs⟩ := exists_finset_affineOpens_cover U₀.left
  -- the affine pieces of the atlas and their fibre bounds
  have hA : ∀ O : s, IsAffine (resOver (O.1 : U₀.left.Opens)).left := fun O => O.1.2
  have hAl : ∀ O : s, LocallyOfFiniteType (resOver (O.1 : U₀.left.Opens)).hom := fun O => by
    change LocallyOfFiniteType ((O.1 : U₀.left.Opens).ι ≫ U₀.hom)
    infer_instance
  have haO : ∀ O : s,
      IsEtale ((schemeYoneda S0).map (resOverι (O.1 : U₀.left.Opens)) ≫ a₀) := fun O =>
    IsEtale.comp (isEtale_map _ (inferInstanceAs (Etale (O.1 : U₀.left.Opens).ι))) ha₀
  choose D hD using fun O : s => @exists_fibre_card_le B hB _ (hA O) _ (haO O)
  let D' := ∑ O, D O
  have hDle : ∀ O, D O ≤ D' := fun O =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ O)
  -- the orbit charts, for every affine piece and every order `r ≤ D'`
  choose n M tM hM htM hMl hMpt using fun p : s × Fin D' =>
    @exists_orbit_charts S0 _ _ B hB _ (hA p.1) (hAl p.1) _ (haO p.1)
      (CyclicGroup.{u} (p.2.val + 1)) _ _
  let I := Σ p : s × Fin D', Fin (n p)
  let e := Fintype.equivFin I
  suffices h : ∀ (κ : Type u) [Field κ] [Finite κ]
      (x : (schemeYoneda S0).obj (toOver (Spec (CommRingCat.of κ))) ⟶ B.presheaf),
      ∃ π : I, ∃ w : toOver (Spec (CommRingCat.of κ)) ⟶ M π.1 π.2,
        (schemeYoneda S0).map w ≫ tM π.1 π.2 = x by
    refine ⟨Fintype.card I, fun j => (M (e.symm j).1 (e.symm j).2).left,
      fun j => (schemeYoneda S0).map (isoToOver _).inv ≫ tM (e.symm j).1 (e.symm j).2,
      fun j => hM _ _, fun j => ?_, fun j => ?_, fun κ _ _ x => ?_⟩
    · rw [specULiftZIsTerminal.hom_ext (specULiftZIsTerminal.from _)
        (M (e.symm j).1 (e.symm j).2).hom]
      exact hMl _ _
    · refine IsEtale.comp (isEtale_map _ ?_) (htM _ _)
      change Etale (𝟙 _)
      infer_instance
    obtain ⟨π, w, hw⟩ := h κ x
    obtain ⟨j, rfl⟩ := e.symm.surjective π
    refine ⟨j, w.left, ?_⟩
    have hw' : toOverHom w.left ≫ (isoToOver _).inv = w := by
      apply Over.OverMorphism.ext
      simp [isoToOver]
    rw [← Functor.map_comp_assoc, hw', hw]
  intro κ _ _ x
  -- a separable point of the atlas over `x`, in an affine piece `O`
  obtain ⟨L, _, _, hL, ℓ, hℓinj, hℓx⟩ := exists_separable_point B ha₀ hs₀ κ x
  have : Finite L := Module.finite_of_finite κ
  have : Finite (L ≃ₐ[κ] L) :=
    Finite.of_injective (fun γ : L ≃ₐ[κ] L => (γ : L → L)) DFunLike.coe_injective
  have : Nonempty (toOver (Spec (CommRingCat.of L))).left :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of L)))
  have : Subsingleton (toOver (Spec (CommRingCat.of L))).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of L)))
  obtain ⟨y₀⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
  obtain ⟨O, hOs, hyO⟩ := hs (ℓ.left y₀)
  obtain ⟨ℓO, hℓO⟩ := exists_factor_resOver (O : U₀.left.Opens) ℓ y₀ hyO
  let Os : s := ⟨O, hOs⟩
  -- the conjugates of `ℓO` under the automorphisms of `L/κ`
  let vΓ : (L ≃ₐ[κ] L) → (toOver (Spec (CommRingCat.of L)) ⟶ resOver (O : U₀.left.Opens)) :=
    fun γ => toOverHom (Spec.map (CommRingCat.ofHom (γ : L →+* L))) ≫ ℓO
  have hvΓinj : Function.Injective vΓ := fun γ γ' h => hℓinj (by
    change toOverHom (Spec.map (CommRingCat.ofHom (γ : L →+* L))) ≫ ℓ =
      toOverHom (Spec.map (CommRingCat.ofHom (γ' : L →+* L))) ≫ ℓ
    rw [← hℓO, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ resOverι (O : U₀.left.Opens)) h)
  have hvΓa : ∀ γ, (schemeYoneda S0).map (vΓ γ) ≫
      (schemeYoneda S0).map (resOverι (Os.1 : U₀.left.Opens)) ≫ a₀ =
        (schemeYoneda S0).map (toOverHom (specMap κ L)) ≫ x := fun γ => by
    change (schemeYoneda S0).map (toOverHom _ ≫ ℓO) ≫
      (schemeYoneda S0).map (resOverι (O : U₀.left.Opens)) ≫ a₀ = _
    rw [← Functor.map_comp_assoc, Category.assoc, hℓO, Functor.map_comp_assoc, hℓx,
      ← Functor.map_comp_assoc, ← toOverHom_comp, specMap_aut_comp]
  -- the degree `r = [L : κ]` is the order of the cyclic group `Aut(L/κ)`, and `r ≤ D'`
  have hcard : Nat.card (L ≃ₐ[κ] L) = Module.finrank κ L := IsGalois.card_aut_eq_finrank κ L
  have hr := hD Os L (L ≃ₐ[κ] L) vΓ hvΓinj fun γ γ' => by rw [hvΓa, hvΓa]
  have hr0 : 0 < Module.finrank κ L := Module.finrank_pos
  have hrD := hDle Os
  let k : Fin D' := ⟨Module.finrank κ L - 1, by omega⟩
  have hGcard : Nat.card (CyclicGroup.{u} (k.val + 1)) = Nat.card (L ≃ₐ[κ] L) := by
    rw [card_cyclicGroup, hcard]
    change Module.finrank κ L - 1 + 1 = Module.finrank κ L
    omega
  let ψ : CyclicGroup.{u} (k.val + 1) ≃* (L ≃ₐ[κ] L) := mulEquivOfCyclicCardEq hGcard
  let σ := specAction (κ := κ) ψ.toMonoidHom
  let v : CyclicGroup.{u} (k.val + 1) →
      (toOver (Spec (CommRingCat.of L)) ⟶ resOver (O : U₀.left.Opens)) := fun g => vΓ (ψ g)
  have hσv : ∀ g g', σ.act g ≫ v g' = v (g * g') := fun g g' => by
    change σ.act g ≫ σ.act g' ≫ ℓO = σ.act (g * g') ≫ ℓO
    rw [← Category.assoc, σ.mul]
  obtain ⟨i, w, hw, hwt⟩ := hMpt (Os, k) (toOver (Spec (CommRingCat.of L))) σ v
    (hvΓinj.comp ψ.injective) hσv fun g => by rw [hvΓa, hvΓa]
  -- the invariant point `w` descends to `κ`
  have : IsAffine (M (Os, k) i).left := hM _ _
  have hwΓ : ∀ γ : L ≃ₐ[κ] L,
      Spec.map (CommRingCat.ofHom (γ : L →+* L)) ≫ w.left = w.left := fun γ => by
    obtain ⟨g, rfl⟩ := ψ.surjective γ
    exact congrArg CommaMorphism.left (hw g)
  obtain ⟨m, hm⟩ := exists_desc_of_aut_invariant w.left hwΓ
  let w' : toOver (Spec (CommRingCat.of κ)) ⟶ M (Os, k) i :=
    Over.homMk m (specULiftZIsTerminal.hom_ext _ _)
  have hw' : toOverHom (specMap κ L) ≫ w' = w := Over.OverMorphism.ext hm
  refine ⟨⟨(Os, k), i⟩, w', ?_⟩
  have : Flat (toOverHom (specMap κ L)).left := inferInstanceAs (Flat (specOver κ L).hom)
  have : LocallyOfFinitePresentation (toOverHom (specMap κ L)).left :=
    inferInstanceAs (LocallyOfFinitePresentation (specOver κ L).hom)
  have : Surjective (toOverHom (specMap κ L)).left :=
    inferInstanceAs (Surjective (specOver κ L).hom)
  refine eq_of_comp_eq B (toOverHom (specMap κ L)) ?_
  rw [← Functor.map_comp_assoc, hw', hwt]
  exact hvΓa (ψ 1)

end Main

end FiniteFieldCharts

end Langlands.AlgebraicGeometry.LangWeil.SpaceFamily
