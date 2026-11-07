import Langlands.AlgebraicGeometry.AlgebraicSpace.SameImageToolkit
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleQuasiFinite
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralCompactness
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # No specializations between points with the same image -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A tower argument: if generalizations lift along `t`, the fibres of `s` contain no
nontrivial specializations, and `t`-`s` moves stay in a finite set, then a pair
`(t r₀, s r₀)` with `s r₀ ⤳ t r₀` is equal. -/
theorem eq_of_specializes_tower {V R : Type*} [TopologicalSpace V] [TopologicalSpace R]
    [T0Space V] (t s : R → V) (ht : GeneralizingMap t) (hs : Continuous s)
    (hsd : ∀ r r', s r = s r' → r ⤳ r' → r = r') {K : Set V} (hK : K.Finite)
    (hKcl : ∀ r, t r ∈ K → s r ∈ K) (r₀ : R) (h₀ : t r₀ ∈ K) (hspec : s r₀ ⤳ t r₀) :
    s r₀ = t r₀ := by
  classical
  by_contra hne
  have step : ∀ r : R, s r ⤳ t r → ∃ r', r' ⤳ r ∧ t r' = s r := fun r h => ht h
  choose next hnext1 hnext2 using step
  let P := {r : R // s r ⤳ t r}
  let nxt : P → P := fun p => ⟨next p.1 p.2, by
    rw [hnext2 p.1 p.2]
    exact (hnext1 p.1 p.2).map hs⟩
  let sq : ℕ → P := fun n => nxt^[n] ⟨r₀, hspec⟩
  have hsq : ∀ n, sq (n + 1) = nxt (sq n) := fun n =>
    Function.iterate_succ_apply' nxt n _
  let w : ℕ → V := fun n => t (sq n).1
  have hw0 : w 0 = t r₀ := rfl
  have hws : ∀ n, w (n + 1) = s (sq n).1 := by
    intro n
    simp only [w, hsq n, nxt]
    exact hnext2 _ _
  have hspecs : ∀ n, (sq (n + 1)).1 ⤳ (sq n).1 := by
    intro n
    rw [hsq n]
    exact hnext1 _ _
  have hwspec : ∀ n, w (n + 1) ⤳ w n := fun n => by
    rw [hws n]
    exact (sq n).2
  have hwK : ∀ n, w n ∈ K := by
    intro n
    induction n with
    | zero => exact h₀
    | succ n ih => rw [hws n]; exact hKcl _ ih
  have hwne : ∀ n, w (n + 1) ≠ w n := by
    intro n
    induction n with
    | zero => rw [hws 0, hw0]; exact hne
    | succ n ih =>
      intro heq
      apply ih
      have h1 : s (sq (n + 1)).1 = s (sq n).1 := by rw [← hws (n + 1), ← hws n]; exact heq
      have h2 := hsd _ _ h1 (hspecs n)
      simp only [w]
      rw [h2]
  have hchain : ∀ i k, w (i + k) ⤳ w i := by
    intro i k
    induction k with
    | zero => exact specializes_rfl
    | succ k ih => exact (hwspec (i + k)).trans ih
  have hinj : Function.Injective w := by
    intro i j hij
    by_contra hij'
    rcases lt_or_gt_of_ne hij' with h | h
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
      have h1 : w (i + k + 1) ⤳ w (i + 1) := by
        have := hchain (i + 1) k
        rwa [show i + 1 + k = i + k + 1 by omega] at this
      rw [← hij] at h1
      exact hwne i ((hwspec i).antisymm h1).eq
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
      have h1 : w (j + k + 1) ⤳ w (j + 1) := by
        have := hchain (j + 1) k
        rwa [show j + 1 + k = j + k + 1 by omega] at this
      rw [hij] at h1
      exact hwne j ((hwspec j).antisymm h1).eq
  exact (Set.infinite_of_injective_forall_mem hinj hwK) hK

/-- Points in a discrete fibre admit no nontrivial specializations. -/
theorem eq_of_specializes_of_isDiscrete {R V : Type*} [TopologicalSpace R] (s : R → V)
    (hs : ∀ v, IsDiscrete (s ⁻¹' {v})) {r r' : R} (h : s r = s r') (hspec : r ⤳ r') :
    r = r' := by
  have hd := (hs (s r')).to_subtype
  have h' : (⟨r, h⟩ : s ⁻¹' {s r'}) ⤳ ⟨r', rfl⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp hspec
  exact congrArg Subtype.val (specializes_iff_eq.mp h')

/-- Locally quasi-finite morphisms admit no specializations inside fibres. -/
theorem eq_of_specializes_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] {x x' : X} (h : f x = f x') (hspec : x ⤳ x') : x = x' :=
  eq_of_specializes_of_isDiscrete f f.isDiscrete_preimage_singleton h hspec

variable {S : Scheme.{u}} {Y : Presheaf S}

set_option backward.isDefEq.respectTransparency.types false in
/-- On an étale chart, points with the same image are not specializations of each other, as
long as the class of a point is contained in a finite set stable under the relation. -/
theorem SameImage.eq_of_specializes_of_etale {V : Over S} {a : (schemeYoneda S).obj V ⟶ Y}
    (ha : IsEtale a) {K : Set V.left} (hK : K.Finite)
    (hKcl : ∀ v v', v ∈ K → SameImage a v v' → v' ∈ K) {v v' : V.left} (hv : v ∈ K)
    (h : SameImage a v v') (hspec : v' ⤳ v) : v' = v := by
  have hr : (schemeYoneda S).relativelyRepresentable a := ha.representable
  obtain ⟨r₀, hr₀t, hr₀s⟩ := SameImage₂.exists_pullback hr h
  have htE : Etale (hr.snd a).left :=
    ha.projection a (hr.fst a) (hr.snd a) (hr.isPullback a)
  have hsE : Etale (hr.fst' a).left :=
    ha.projection a ((schemeYoneda S).map (hr.snd a)) (hr.fst' a) (hr.isPullback' a).flip
  have hLQF : LocallyQuasiFinite (hr.fst' a).left := locallyQuasiFinite_of_etale _
  have := eq_of_specializes_tower (hr.snd a).left (hr.fst' a).left
    (Flat.generalizingMap _) (hr.fst' a).left.continuous
    (fun r r' h1 h2 => eq_of_specializes_of_locallyQuasiFinite _ h1 h2) hK
    (fun r hr' => hKcl _ _ hr' (SameImage₂.of_pullback hr r)) r₀ (hr₀t ▸ hv)
    (by rw [hr₀t, hr₀s]; exact hspec)
  rw [← hr₀t, ← hr₀s]
  exact this

set_option backward.isDefEq.respectTransparency.types false in
/-- Classes of an étale chart are finite when a finite surjective map from a quasi-compact
quasi-separated scheme covers the target. -/
theorem SameImage.finite_of_cover {U V : Over S} {f : (schemeYoneda S).obj U ⟶ Y}
    (hf : IsFinite f) (hfs : IsSurjective f) [CompactSpace U.left]
    [QuasiSeparatedSpace U.left] {a : (schemeYoneda S).obj V ⟶ Y} (ha : IsEtale a)
    [CompactSpace V.left] (v : V.left) : {w | SameImage a v w}.Finite := by
  have hfr : (schemeYoneda S).relativelyRepresentable f := hf.representable
  let πV := hfr.snd a
  let πU := hfr.fst' a
  have hπVs : Surjective πV.left := hfs.projection a (hfr.fst a) πV (hfr.isPullback a)
  have hπVf : _root_.AlgebraicGeometry.IsFinite πV.left :=
    hf.projection a (hfr.fst a) πV (hfr.isPullback a)
  have hπUe : Etale πU.left :=
    ha.projection f ((schemeYoneda S).map πV) πU (hfr.isPullback' a).flip
  have : LocallyQuasiFinite πU.left := locallyQuasiFinite_of_etale _
  have : CompactSpace (hfr.pullback a).left :=
    QuasiCompact.compactSpace_of_compactSpace πV.left
  have : QuasiCompact πU.left := (quasiCompact_iff_compactSpace πU.left).mpr inferInstance
  obtain ⟨p₀, hp₀⟩ := hπVs.surj v
  refine ((πU.left.finite_preimage_singleton (πU.left p₀)).image πV.left).subset ?_
  intro w hw
  have h1 : SameImage₂ a f (πV.left p₀) (πU.left p₀) := SameImage₂.of_pullback hfr p₀
  rw [hp₀] at h1
  have h2 : SameImage₂ a f w (πU.left p₀) := (SameImage₂.symm hw).trans h1
  obtain ⟨p, hp1, hp2⟩ := SameImage₂.exists_pullback hfr h2
  exact ⟨p, hp2, hp1⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Points of a quasi-compact quasi-separated scheme with the same image under a finite
surjective map to a quasi-compact algebraic space are not specializations of each other. -/
theorem SameImage.eq_of_specializes {U : Over S} {X : AlgebraicSpace S}
    {f : (schemeYoneda S).obj U ⟶ X.presheaf} (hf : IsFinite f) (hfs : IsSurjective f)
    (hX : IsQuasiCompact X) [CompactSpace U.left] [QuasiSeparatedSpace U.left] {x y : U.left}
    (h : SameImage f x y) (hspec : x ⤳ y) : x = y := by
  obtain ⟨V, a, ha, has, hV⟩ := hX
  have : CompactSpace V.left := hV
  have hfr : (schemeYoneda S).relativelyRepresentable f := hf.representable
  let πV := hfr.snd a
  let πU := hfr.fst' a
  have hπVf : _root_.AlgebraicGeometry.IsFinite πV.left :=
    hf.projection a (hfr.fst a) πV (hfr.isPullback a)
  have hπUe : Etale πU.left :=
    ha.projection f ((schemeYoneda S).map πV) πU (hfr.isPullback' a).flip
  have hπUs : Surjective πU.left :=
    has.projection f ((schemeYoneda S).map πV) πU (hfr.isPullback' a).flip
  obtain ⟨yP, hyP⟩ := hπUs.surj y
  obtain ⟨xP, hxPy, hxP⟩ := Flat.generalizingMap πU.left (hyP ▸ hspec)
  have hvspec : πV.left xP ⤳ πV.left yP := hxPy.map πV.left.continuous
  have hsame : SameImage a (πV.left yP) (πV.left xP) := by
    have h1 : SameImage₂ a f (πV.left xP) (πU.left xP) := SameImage₂.of_pullback hfr xP
    have h2 : SameImage₂ a f (πV.left yP) (πU.left yP) := SameImage₂.of_pullback hfr yP
    rw [hxP] at h1
    rw [hyP] at h2
    exact (h2.trans (SameImage₂.symm h)).trans h1.symm
  have hvv : πV.left xP = πV.left yP :=
    SameImage.eq_of_specializes_of_etale ha
      (SameImage.finite_of_cover hf hfs ha (πV.left yP))
      (fun v v' hv hvv' => SameImage.trans hv hvv') (SameImage.refl a _) hsame hvspec
  have : xP = yP := eq_of_specializes_of_locallyQuasiFinite πV.left hvv hxPy
  rw [← hxP, ← hyP, this]

end Langlands.AlgebraicGeometry.AlgebraicSpace
