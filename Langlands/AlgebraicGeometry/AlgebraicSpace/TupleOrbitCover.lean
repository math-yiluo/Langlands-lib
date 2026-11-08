import Langlands.AlgebraicGeometry.AlgebraicSpace.TupleOrbitLoci
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Tuple covers whose fibres are permutation orbits away from a proper closed set -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A scheme finite over a Noetherian scheme is Noetherian. -/
theorem isNoetherian_of_isFinite {X Z : Scheme.{u}} (g : X ⟶ Z)
    [_root_.AlgebraicGeometry.IsFinite g] [_root_.AlgebraicGeometry.IsNoetherian Z] :
    _root_.AlgebraicGeometry.IsNoetherian X :=
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian g
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace g }

variable {S : Scheme.{u}} {U : Over S} {Y : AlgebraicSpace S}
  {f : (schemeYoneda S).obj U ⟶ Y.presheaf}

/-- A point whose class is closed under generization exists. -/
theorem exists_generic_sameImage (hf : IsFinite f) (hfs : IsSurjective f) (hY : IsQuasiCompact Y)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left] [NoetherianSpace U.left]
    (hne : Nonempty U.left) :
    ∃ γ : U.left, ∀ a b, a ⤳ b → SameImage f b γ → SameImage f a γ := by
  let G : Set U.left := (fun g => closure ({g} : Set U.left)) ⁻¹' irreducibleComponents U.left
  have hG : G.Finite := by
    refine NoetherianSpace.finite_irreducibleComponents.preimage ?_
    intro g _ g' _ h
    exact (inseparable_iff_closure_eq.mpr h).eq
  have hgen : ∀ x : U.left, ∃ g ∈ G, g ⤳ x := by
    intro x
    have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
    have hgp := hirr.isGenericPoint_genericPoint isClosed_irreducibleComponent
    refine ⟨hirr.genericPoint, ?_, hgp.specializes mem_irreducibleComponent⟩
    show closure {hirr.genericPoint} ∈ irreducibleComponents U.left
    rw [hgp.def]
    exact irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨x₀⟩ := hne
  obtain ⟨g₀, hg₀, -⟩ := hgen x₀
  obtain ⟨γ, -, hγ⟩ := exists_generic_class (SameImage f) (sameImage_equivalence f)
    (fun a b h hab => SameImage.eq_of_specializes hf hfs hY h hab)
    (fun x x' y h hxy => SameImage.exists_specializes hf h hxy) hG ⟨g₀, hg₀⟩ hgen
  exact ⟨γ, hγ⟩

/-- Distinct tuples with a coordinate at `γ` transfer between fibre powers with the same index
type. -/
theorem ChartFibrePower.exists_isDistinct_transfer {ι : Type*} (Q Q' : ChartFibrePower f ι)
    (γ : U.left) {q : Q.obj.left} (hq : Q.IsDistinct q) {i : ι} (hi : (Q.pr i).left q = γ) :
    Q'.IsDistinct ((Q.mapIndex Q' id).left q) ∧ (Q'.pr i).left ((Q.mapIndex Q' id).left q) = γ := by
  refine ⟨fun a b hab => hq ((ChartFibrePower.coord_mapIndex_eq_iff Q Q' id q a b).mp hab), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ChartFibrePower.mapIndex_pr]
  exact hi

/-- The maximal length of distinct tuples through `γ`. -/
theorem exists_max_isDistinct (hf : IsFinite f) (γ : U.left) :
    ∃ k : ℕ, (∃ (Q : ChartFibrePower f (Fin (k + 1))) (q : Q.obj.left),
        Q.IsDistinct q ∧ ∃ i, (Q.pr i).left q = γ) ∧
      ∀ (Q : ChartFibrePower f (Fin (k + 2))) (q : Q.obj.left), Q.IsDistinct q →
        ∀ i, (Q.pr i).left q ≠ γ := by
  classical
  obtain ⟨N, hN⟩ := exists_bound_isDistinct hf γ
  let pred : ℕ → Prop := fun m => ∃ (Q : ChartFibrePower f (Fin m)) (q : Q.obj.left),
    Q.IsDistinct q ∧ ∃ i, (Q.pr i).left q = γ
  have h1 : pred 1 := ⟨ChartFibrePower.one f, γ, fun a b _ => Subsingleton.elim a b, 0, rfl⟩
  have h1N : 1 ≤ N := by
    obtain ⟨Q, q, hq, hi⟩ := h1
    exact hN 1 Q q hq hi
  let n := Nat.findGreatest pred N
  have hn1 : 1 ≤ n := Nat.le_findGreatest h1N h1
  have hpn : pred n := Nat.findGreatest_spec h1N h1
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨k, hk ▸ hpn, fun Q q hq i hi => ?_⟩
  by_cases hkN : k + 2 ≤ N
  · exact Nat.findGreatest_is_greatest (show n < k + 2 by omega) hkN ⟨Q, q, hq, i, hi⟩
  · have := hN (k + 2) Q q hq ⟨i, hi⟩
    omega

variable (f) in
/-- The output of the tuple-orbit construction: a fibre power `P` of `f`, a closed
permutation-stable set `Wset` of tuples meeting every class, and a proper saturated closed set
`C` of points away from which the classes of tuples in `Wset` are permutation orbits. -/
structure TupleOrbitCover where
  /-- The tuples have length `k + 1`. -/
  k : ℕ
  /-- The fibre power. -/
  P : ChartFibrePower f (Fin (k + 1))
  pr_isFinite : ∀ i, _root_.AlgebraicGeometry.IsFinite (P.pr i).left
  /-- The closed set of tuples. -/
  Wset : Set P.obj.left
  isClosed_Wset : IsClosed Wset
  perm_mem : ∀ (σ : Equiv.Perm (Fin (k + 1))) (w : P.obj.left), w ∈ Wset →
    (P.perm σ).left w ∈ Wset
  surj : ∀ u : U.left, ∃ w ∈ Wset, SameImage f u ((P.pr 0).left w)
  /-- The bad closed set. -/
  C : Set U.left
  isClosed_C : IsClosed C
  saturated_C : ∀ u u', SameImage f u u' → u ∈ C → u' ∈ C
  exists_notMem : ∃ u, u ∉ C
  orbit : ∀ w ∈ Wset, ∀ w' ∈ Wset, (P.pr 0).left w ∉ C →
    SameImage ((schemeYoneda S).map (P.pr 0) ≫ f) w w' → ∃ σ, (P.perm σ).left w = w'

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
/-- The tuple-orbit construction exists for a finite surjective map from a nonempty
quasi-compact quasi-separated Noetherian scheme to a quasi-compact algebraic space. -/
theorem exists_tupleOrbitCover (hf : IsFinite f) (hfs : IsSurjective f) (hY : IsQuasiCompact Y)
    [_root_.AlgebraicGeometry.IsNoetherian U.left] [QuasiSeparatedSpace U.left]
    (hne : Nonempty U.left) : Nonempty (TupleOrbitCover f) := by
  classical
  have ha : (schemeYoneda S).relativelyRepresentable f := hf.representable
  obtain ⟨γ, hγ⟩ := exists_generic_sameImage hf hfs hY hne
  obtain ⟨k, ⟨Q₀, q₀, hq₀, i₀, hi₀⟩, hmax⟩ := exists_max_isDistinct hf γ
  let P := ChartFibrePower.fin ha k
  have hPfin : ∀ i, _root_.AlgebraicGeometry.IsFinite (P.pr i).left :=
    ChartFibrePower.fin_pr_isFinite hf ha k
  let e : Fin (k + 1) ⊕ Fin (k + 1) ≃ Fin (2 * k + 1 + 1) :=
    finSumFinEquiv.trans (finCongr (by omega))
  let P2 : ChartFibrePower f (Fin (k + 1) ⊕ Fin (k + 1)) :=
    (ChartFibrePower.fin ha (2 * k + 1)).reindex e
  have hP2fin : ∀ j, _root_.AlgebraicGeometry.IsFinite (P2.pr j).left := fun j =>
    ChartFibrePower.fin_pr_isFinite hf ha (2 * k + 1) (e j)
  have : _root_.AlgebraicGeometry.IsNoetherian P.obj.left := by
    have := hPfin 0
    exact isNoetherian_of_isFinite (P.pr 0).left
  have : _root_.AlgebraicGeometry.IsNoetherian P2.obj.left := by
    have := hP2fin (Sum.inl 0)
    exact isNoetherian_of_isFinite (P2.pr (Sum.inl 0)).left
  let Q1 := ChartFibrePower.fin ha (k + 1)
  let pr := P.pr 0
  let inl := P2.mapIndex P Sum.inl
  let inr := P2.mapIndex P Sum.inr
  -- the locally closed set of distinct tuples through the closure of `γ`
  let Hγ : Set P.obj.left := ⋃ i, (P.pr i).left ⁻¹' closure {γ}
  have hHγ : IsClosed Hγ := isClosed_iUnion_of_finite fun i =>
    isClosed_closure.preimage (P.pr i).left.continuous
  let Dd : Set P.obj.left := {p | P.IsDistinct p}
  have hDd : IsOpen Dd := ChartFibrePower.isOpen_isDistinct hf P
  let D := Hγ ∩ Dd
  obtain ⟨hd₀, hd₀i⟩ := ChartFibrePower.exists_isDistinct_transfer Q₀ P γ hq₀ hi₀
  set d₀ := (Q₀.mapIndex P id).left q₀
  have hd₀D : d₀ ∈ D := ⟨Set.mem_iUnion.mpr ⟨i₀, by
    rw [Set.mem_preimage, hd₀i]; exact subset_closure rfl⟩, hd₀⟩
  let A : Set U.left := pr.left '' closure D
  let O : Set U.left := (saturation f A)ᶜ
  have hO : IsOpen O := (isClosed_saturation hf (pr.left.isClosedMap _ isClosed_closure)).isOpen_compl
  let C₂ := saturation f (closure O)
  have hC₂ : IsClosed C₂ := isClosed_saturation hf isClosed_closure
  have hγA : γ ∈ saturation f A :=
    ⟨pr.left d₀, ⟨d₀, subset_closure hd₀D, rfl⟩, by
      have := ChartFibrePower.sameImage_pr P d₀ 0 i₀
      rwa [hd₀i] at this⟩
  have hγC₂ : γ ∉ C₂ := by
    rintro ⟨x, hx, hxγ⟩
    have hx' : x ∈ closure (Set.univ ∩ O) := by rwa [Set.univ_inter]
    obtain ⟨o, ⟨-, ho⟩, hox⟩ := exists_mem_specializes_of_mem_closure isClosed_univ hO hx'
    exact ho (saturation_saturated f A hγA (hγ o x hox hxγ).symm)
  let δ := P.diag
  have hδ : _root_.AlgebraicGeometry.IsClosedImmersion δ.left :=
    ChartFibrePower.diag_isClosedImmersion P 0 (hPfin 0)
  let Wset : Set P.obj.left := closure D ∪ δ.left '' C₂
  have hWset : IsClosed Wset :=
    isClosed_closure.union (hδ.isClosedEmbedding.isClosedMap _ hC₂)
  have hprδ : ∀ x, pr.left (δ.left x) = x := fun x => by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ChartFibrePower.diag_pr]; rfl
  -- points of `Wset` over the class of `γ` are distinct tuples through `γ`
  have keyW : ∀ w ∈ Wset, SameImage f (pr.left w) γ →
      P.IsDistinct w ∧ ∃ i, (P.pr i).left w = γ := by
    intro w hw hwγ
    rcases hw with hw | ⟨x, hx, rfl⟩
    · obtain ⟨d, ⟨hdH, hdD⟩, hdw⟩ := exists_mem_specializes_of_mem_closure hHγ hDd hw
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hdH
      rw [Set.mem_preimage, ← specializes_iff_mem_closure] at hi
      have h1 : γ ⤳ (P.pr i).left w := hi.trans (hdw.map (P.pr i).left.continuous)
      have h2 : SameImage f γ ((P.pr i).left w) :=
        hwγ.symm.trans (ChartFibrePower.sameImage_pr P w 0 i)
      have h3 : γ = (P.pr i).left w := SameImage.eq_of_specializes hf hfs hY h2 h1
      have h4 : (P.pr i).left d = γ :=
        ((h3 ▸ (hdw.map (P.pr i).left.continuous)).antisymm hi).eq
      have h5 : d = w := eq_of_specializes_of_locallyQuasiFinite (P.pr i).left
        (h4.trans h3) hdw
      exact ⟨h5 ▸ hdD, i, h3.symm⟩
    · exact absurd (saturation_saturated f _ hx (by rwa [hprδ] at hwγ)) hγC₂
  -- pigeonhole on pairs over the class of `γ`
  have keyP : ∀ q : P2.obj.left, P.IsDistinct (inl.left q) → P.IsDistinct (inr.left q) →
      (∃ i, (P.pr i).left (inl.left q) = γ) →
      ∃ π : Equiv.Perm (Fin (k + 1)), ∀ i, P2.coord q (Sum.inr i) = P2.coord q (Sum.inl (π i)) := by
    intro q hl hr ⟨j₀, hj₀⟩
    let x : Fin (k + 1) → _ := fun i => P2.coord q (Sum.inl i)
    let y : Fin (k + 1) → _ := fun i => P2.coord q (Sum.inr i)
    have hx : Function.Injective x := fun a b hab =>
      hl ((ChartFibrePower.coord_mapIndex_eq_iff P2 P Sum.inl q a b).mpr hab)
    have hy : Function.Injective y := fun a b hab =>
      hr ((ChartFibrePower.coord_mapIndex_eq_iff P2 P Sum.inr q a b).mpr hab)
    obtain ⟨π, hπ⟩ := exists_perm_of_not_injective_snoc x y hx hy (by
      intro b hinj
      let e' : Fin (k + 2) → Fin (k + 1) ⊕ Fin (k + 1) :=
        Fin.snoc (α := fun _ => Fin (k + 1) ⊕ Fin (k + 1)) (fun i => Sum.inl i) (Sum.inr b)
      have hcoord : ∀ a, P2.coord q (e' a) = (Fin.snoc x (y b) : Fin (k + 2) → _) a := by
        intro a
        induction a using Fin.lastCases with
        | last => simp [e', y]
        | cast i => simp [e', x]
      let q1 := (P2.mapIndex Q1 e').left q
      have hq1 : Q1.IsDistinct q1 := by
        intro a c hac
        rw [ChartFibrePower.coord_mapIndex_eq_iff P2 Q1 e' q a c, hcoord, hcoord] at hac
        exact hinj hac
      apply hmax Q1 q1 hq1 (Fin.castSucc j₀)
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ChartFibrePower.mapIndex_pr]
      have : e' (Fin.castSucc j₀) = Sum.inl j₀ := by simp [e']
      rw [this, ← ChartFibrePower.mapIndex_pr P2 P Sum.inl j₀, Over.comp_left,
        Scheme.Hom.comp_apply]
      exact hj₀)
    exact ⟨π, hπ⟩
  -- the bad set
  let Hset : Set P2.obj.left := inl.left ⁻¹' Wset ∩ inr.left ⁻¹' Wset
  have hHset : IsClosed Hset := (hWset.preimage inl.left.continuous).inter
    (hWset.preimage inr.left.continuous)
  let Graph : Set P2.obj.left := ⋃ π : Equiv.Perm (Fin (k + 1)),
    ⋂ i, {p | P2.coord p (Sum.inr i) = P2.coord p (Sum.inl (π i))}
  have hGraph : IsClosed Graph := isClosed_iUnion_of_finite fun π =>
    isClosed_iInter fun i => ChartFibrePower.isClosed_coord_eq hf P2 _ _
  let Qset := Hset ∩ Graphᶜ
  let pr2 := P2.pr (Sum.inr 0)
  let Bad := saturation f (pr2.left '' closure Qset)
  have hBad : IsClosed Bad := by
    have := hP2fin (Sum.inr 0)
    exact isClosed_saturation hf (pr2.left.isClosedMap _ isClosed_closure)
  have hprinr : ∀ p, pr.left (inr.left p) = pr2.left p := fun p => by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ChartFibrePower.mapIndex_pr]
  have hprinl : ∀ p, pr.left (inl.left p) = (P2.pr (Sum.inl 0)).left p := fun p => by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ChartFibrePower.mapIndex_pr]
  have hγBad : γ ∉ Bad := by
    rintro ⟨y, ⟨x, hx, rfl⟩, hyγ⟩
    obtain ⟨q, ⟨hqH, hqG⟩, hqx⟩ := exists_mem_specializes_of_mem_closure hHset
      hGraph.isOpen_compl hx
    have h1 : SameImage f (pr2.left q) γ := hγ _ _ (hqx.map pr2.left.continuous) hyγ
    have hr : SameImage f (pr.left (inr.left q)) γ := by rw [hprinr]; exact h1
    have hl : SameImage f (pr.left (inl.left q)) γ := by
      rw [hprinl]
      exact (ChartFibrePower.sameImage_pr P2 q (Sum.inl 0) (Sum.inr 0)).trans h1
    obtain ⟨hld, hli⟩ := keyW _ hqH.1 hl
    obtain ⟨hrd, -⟩ := keyW _ hqH.2 hr
    obtain ⟨π, hπ⟩ := keyP q hld hrd hli
    exact hqG (Set.mem_iUnion.mpr ⟨π, Set.mem_iInter.mpr fun i => hπ i⟩)
  have hDperm : ∀ (σ : Equiv.Perm (Fin (k + 1))) d, d ∈ D → (P.perm σ).left d ∈ D := by
    rintro σ d ⟨hdH, hdD⟩
    refine ⟨?_, (ChartFibrePower.isDistinct_perm_iff P σ d).mpr hdD⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hdH
    refine Set.mem_iUnion.mpr ⟨σ.symm i, ?_⟩
    rw [Set.mem_preimage, ChartFibrePower.pr_perm_apply, Equiv.apply_symm_apply]
    exact hi
  have hγC : γ ∉ Bad ∪ C₂ := fun h => Or.elim h hγBad hγC₂
  refine ⟨⟨k, P, hPfin, Wset, hWset, ?_, ?_, Bad ∪ C₂, hBad.union hC₂, ?_, ⟨γ, hγC⟩, ?_⟩⟩
  · intro σ w hw
    rcases hw with hw | ⟨x, hx, rfl⟩
    · left
      have hcont := (P.perm σ).left.continuous
      refine (closure_mono ?_) (image_closure_subset_closure_image hcont ⟨w, hw, rfl⟩)
      rintro _ ⟨d, hd, rfl⟩
      exact hDperm σ d hd
    · right
      refine ⟨x, hx, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ChartFibrePower.diag_perm]
  · intro u
    by_cases hu : u ∈ saturation f A
    · obtain ⟨_, ⟨w, hw, rfl⟩, hwu⟩ := hu
      exact ⟨w, Or.inl hw, hwu.symm⟩
    · have huC : u ∈ C₂ := subset_saturation f _ (subset_closure hu)
      exact ⟨δ.left u, Or.inr ⟨u, huC, rfl⟩, by rw [hprδ]; exact SameImage.refl f u⟩
  · intro u u' h hu
    rcases hu with hu | hu
    · exact Or.inl (saturation_saturated f _ hu h)
    · exact Or.inr (saturation_saturated f _ hu h)
  · intro w hw w' hw' hwC h
    obtain ⟨p, hpl, hpr⟩ := ChartFibrePower.exists_pair P P2 0 h
    by_cases hp : p ∈ Graph
    · obtain ⟨π, hπ⟩ := Set.mem_iUnion.mp hp
      refine ⟨π, ?_⟩
      have := ChartFibrePower.inr_eq_perm_inl P P2 π p fun i => Set.mem_iInter.mp hπ i
      rw [← hpl, ← hpr]
      exact this.symm
    · exfalso
      have hpQ : p ∈ Qset :=
        ⟨⟨show (P2.mapIndex P Sum.inl).left p ∈ Wset by rw [hpl]; exact hw,
          show (P2.mapIndex P Sum.inr).left p ∈ Wset by rw [hpr]; exact hw'⟩, hp⟩
      have hpBad : pr2.left p ∈ Bad := subset_saturation f _ ⟨p, subset_closure hpQ, rfl⟩
      have h1 : SameImage f (pr.left w) (pr.left w') := by
        have h2 := SameImage₂.of_comp pr h
        have h3 := SameImage₂.of_comp pr h2.symm
        exact h3.symm
      have h4 : pr2.left p = pr.left w' := by rw [← hprinr, hpr]
      exact hwC (Or.inl (saturation_saturated f _ hpBad (h4 ▸ h1.symm)))

end Langlands.AlgebraicGeometry.AlgebraicSpace
