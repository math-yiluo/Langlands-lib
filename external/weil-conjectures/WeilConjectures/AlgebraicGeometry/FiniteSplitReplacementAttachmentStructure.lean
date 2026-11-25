/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementAttachmentConstruction
import Mathlib.AlgebraicGeometry.LimitsOver

/-! Split hypercover data on the explicitly constructed simplicial attachment. -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.SchemeSplitAttachment

-- Transport a coproduct cofan along isomorphisms of its summands and vertex.
private def cofan_colimit_of_iso {I : Type*} {C : Type*} [Category C]
    {f g : I → C} (c : Cofan f) (d : Cofan g) (e : ∀ i, f i ≅ g i)
    (t : c.pt ≅ d.pt) (h : ∀ i, c.inj i ≫ t.hom = (e i).hom ≫ d.inj i)
    (hd : IsColimit d) : IsColimit c := by
  let legs (s : Cofan f) (i : I) := (e i).inv ≫ s.inj i
  refine Cofan.IsColimit.mk c
    (fun s ↦ t.hom ≫ Cofan.IsColimit.desc hd (legs s)) ?_ ?_
  · intro s i
    rw [← Category.assoc, h, Category.assoc, Cofan.IsColimit.fac]
    simp only [legs, Iso.hom_inv_id_assoc]
  · intro s m hm
    apply (cancel_epi t.inv).mp
    simp only [Iso.inv_hom_id_assoc]
    apply Cofan.IsColimit.hom_ext hd
    intro i
    have h' : d.inj i ≫ t.inv = (e i).inv ≫ c.inj i := by
      apply (cancel_epi (e i).hom).mp
      rw [← Category.assoc, ← h]
      simp
    rw [← Category.assoc, h', Category.assoc, hm, Cofan.IsColimit.fac]

private theorem lastCases_mk {k : ℕ} {P : Fin (k + 1) → Sort*}
    (a : P (Fin.last k)) (f : ∀ q : Fin k, P q.castSucc)
    (q : Fin k) (h : q.val < k + 1) : Fin.lastCases (motive := P) a f ⟨q.val, h⟩ = f q :=
  Fin.lastCases_castSucc (motive := P) q

-- Bundle the object and inclusion so that degreewise case analysis preserves their types.
private structure NondegDegree {X : Scheme.{u}} {n : ℕ}
    (S : SimplicialObject.Truncated X.Etale n)
    (q : Fin (n + 1)) where
  N : X.Etale
  inc : N ⟶ S.obj (op ⟨SimplexCategory.mk q.val, Nat.le_of_lt_succ q.isLt⟩)

private theorem inc_of_eq {X : Scheme.{u}} {n : ℕ} {S : SimplicialObject.Truncated X.Etale n}
    {q : Fin (n + 1)} {a b : NondegDegree S q} (h : a = b) :
    a.inc = eqToHom (congrArg NondegDegree.N h) ≫ b.inc := by
  cases h
  simp

private def extNondeg {X : Scheme.{u}} {n : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X n)
    (S : SimplicialObject.Truncated X.Etale (n + 1))
    (hs : (SimplicialObject.Truncated.trunc X.Etale (n + 1) n).obj S = U.simplicial)
    (V : X.Etale) (ι : V ⟶ S.obj (op ⟨SimplexCategory.mk (n + 1), le_rfl⟩)) :
    ∀ q : Fin (n + 1 + 1), NondegDegree S q :=
  Fin.lastCases (motive := NondegDegree S) ⟨V, ι⟩ (fun q ↦ ⟨U.N q, U.inclusion q ≫ eqToHom (by
    rw [← hs]; rfl)⟩)

-- Matching data in one degree, including the universal property in the category over X.
private structure MatchingDegree {X : Scheme.{u}} {n : ℕ}
    (S : SimplicialObject.Truncated X.Etale n)
    (q : Fin (n + 1)) where
  M : X.Etale
  π : ∀ (Δ : SimplexCategory.Truncated n), Δ.obj.len < q.val →
    (Δ.obj ⟶ SimplexCategory.mk q.val) → (M ⟶ S.obj (op Δ))
  naturality : ∀ (Δ Δ' : SimplexCategory.Truncated n)
    (h : Δ.obj.len < q.val) (h' : Δ'.obj.len < q.val) (α : Δ' ⟶ Δ)
    (θ : Δ.obj ⟶ SimplexCategory.mk q.val),
    π Δ h θ ≫ S.map α.op = π Δ' h' (α.hom ≫ θ)
  universal : ∀ (T : Over X)
    (p : ∀ (Δ : SimplexCategory.Truncated n), Δ.obj.len < q.val →
      (Δ.obj ⟶ SimplexCategory.mk q.val) →
        (T ⟶ (Scheme.Etale.forget X).obj (S.obj (op Δ)))),
    (∀ (Δ Δ' : SimplexCategory.Truncated n)
      (h : Δ.obj.len < q.val) (h' : Δ'.obj.len < q.val) (α : Δ' ⟶ Δ)
      (θ : Δ.obj ⟶ SimplexCategory.mk q.val),
      p Δ h θ ≫ (Scheme.Etale.forget X).map (S.map α.op) =
        p Δ' h' (α.hom ≫ θ)) →
    ∃! f : T ⟶ (Scheme.Etale.forget X).obj M,
      ∀ (Δ : SimplexCategory.Truncated n) (h : Δ.obj.len < q.val)
        (θ : Δ.obj ⟶ SimplexCategory.mk q.val),
        f ≫ (Scheme.Etale.forget X).map (π Δ h θ) = p Δ h θ
  μ : S.obj (op ⟨SimplexCategory.mk q.val, Nat.le_of_lt_succ q.isLt⟩) ⟶ M
  fac : ∀ (Δ : SimplexCategory.Truncated n) (h : Δ.obj.len < q.val)
    (θ : Δ.obj ⟶ SimplexCategory.mk q.val), μ ≫ π Δ h θ =
      S.map (SimplexCategory.Truncated.Hom.tr θ Δ.property
        (Nat.le_of_lt_succ q.isLt)).op
  cover : Surjective μ.left

private def lowerMatching {X : Scheme.{u}} {n : ℕ}
    (S : SimplicialObject.Truncated X.Etale (n + 1))
    (q : Fin (n + 1)) (D : MatchingDegree S q.castSucc) :
    MatchingDegree ((SimplicialObject.Truncated.trunc X.Etale (n + 1) n).obj S) q where
  M := D.M
  π Δ h θ := D.π ⟨Δ.obj, Δ.property.trans (Nat.le_succ n)⟩ h θ
  naturality Δ Δ' h h' α θ := D.naturality _ _ h h'
    (SimplexCategory.Truncated.Hom.tr α.hom _ _) θ
  universal T p hp := by
    let p' (Δ : SimplexCategory.Truncated (n + 1)) (h : Δ.obj.len < q.val)
        (θ : Δ.obj ⟶ SimplexCategory.mk q.val) :=
      p ⟨Δ.obj, (Nat.le_of_lt h).trans (Nat.le_of_lt_succ q.isLt)⟩ h θ
    have hp' (Δ Δ' : SimplexCategory.Truncated (n + 1))
        (h : Δ.obj.len < q.val) (h' : Δ'.obj.len < q.val) (α : Δ' ⟶ Δ)
        (θ : Δ.obj ⟶ SimplexCategory.mk q.val) :
        p' Δ h θ ≫ (Scheme.Etale.forget X).map (S.map α.op) =
          p' Δ' h' (α.hom ≫ θ) :=
      hp _ _ h h' (SimplexCategory.Truncated.Hom.tr α.hom _ _) θ
    obtain ⟨f, hf, huniq⟩ := D.universal T p' hp'
    refine ⟨f, ?_, ?_⟩
    · intro Δ h θ
      exact hf ⟨Δ.obj, Δ.property.trans (Nat.le_succ n)⟩ h θ
    · intro g hg
      apply huniq g
      intro Δ h θ
      exact hg ⟨Δ.obj, (Nat.le_of_lt h).trans (Nat.le_of_lt_succ q.isLt)⟩ h θ
  μ := D.μ
  fac Δ h θ := D.fac ⟨Δ.obj, Δ.property.trans (Nat.le_succ n)⟩ h θ
  cover := D.cover

private def nondegOf {X : Scheme.{u}} {n : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X n) (q : Fin (n + 1)) :
    NondegDegree U.simplicial q := ⟨U.N q, U.inclusion q⟩
private def matchingOf {X : Scheme.{u}} {n : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X n) (q : Fin (n + 1)) :
    MatchingDegree U.simplicial q :=
  ⟨U.matching q, U.projection q, U.projection_naturality q, U.matching_universal q,
    U.matchingMap q, U.matchingMap_projection q, U.matching_cover q⟩
private theorem inc_heq {X : Scheme.{u}} {n : ℕ}
    {S : SimplicialObject.Truncated X.Etale n} {q : Fin (n + 1)}
    {a b : NondegDegree S q} (h : a = b) : HEq a.inc b.inc := by cases h; rfl
private theorem π_heq {X : Scheme.{u}} {n : ℕ}
    {S : SimplicialObject.Truncated X.Etale n} {q : Fin (n + 1)}
    {a b : MatchingDegree S q} (h : a = b) : HEq a.π b.π := by cases h; rfl
private theorem μ_heq {X : Scheme.{u}} {n : ℕ}
    {S : SimplicialObject.Truncated X.Etale n} {q : Fin (n + 1)}
    {a b : MatchingDegree S q} (h : a = b) : HEq a.μ b.μ := by cases h; rfl
-- Only the two bundles contain data; all remaining fields are unique or proofs.
private theorem structure_ext {X : Scheme.{u}} {n : ℕ}
    (U V : TruncatedFiniteSplitEtaleHypercover X n)
    (hs : U.simplicial = V.simplicial)
    (ha : HEq (nondegOf U) (nondegOf V))
    (hd : HEq (matchingOf U) (matchingOf V)) : U = V := by
  rcases U with ⟨S, N, inc, split, finite, M, π, hn, hu, μ, hμ, hc⟩
  rcases V with ⟨S', N', inc', split', finite', M', π', hn', hu', μ', hμ', hc'⟩
  dsimp only at hs
  subst S'
  have ha := eq_of_heq ha
  have hd := eq_of_heq hd
  have hN : N = N' := congrArg (fun A ↦ fun q ↦ (A q).N) ha
  subst N'
  have hi : inc = inc' := funext (fun q ↦ eq_of_heq (inc_heq (congrFun ha q)))
  subst inc'
  have hM : M = M' := congrArg (fun A ↦ fun q ↦ (A q).M) hd
  subst M'
  have hπ : π = π' := funext (fun q ↦ eq_of_heq (π_heq (congrFun hd q)))
  subst π'
  have hμ : μ = μ' := funext (fun q ↦ eq_of_heq (μ_heq (congrFun hd q)))
  subst μ'
  congr 1
  exact Subsingleton.elim _ _

-- Extend arbitrary compatible top-degree data, keeping the lower data literally unchanged.
private theorem extend_structure {X : Scheme.{u}} {n : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X n)
    (S : SimplicialObject.Truncated X.Etale (n + 1))
    (hs : (SimplicialObject.Truncated.trunc X.Etale (n + 1) n).obj S = U.simplicial)
    (V : X.Etale) (ι : V ⟶ S.obj (op ⟨SimplexCategory.mk (n + 1), le_rfl⟩))
    (hsplit : IsColimit (Cofan.mk (S.obj (op ⟨SimplexCategory.mk (n + 1), le_rfl⟩))
      (fun a : Labels (n + 1) (n + 1) ↦
        (extNondeg U S hs V ι a.1).inc ≫ S.map (SimplexCategory.Truncated.Hom.tr
          a.2.val le_rfl (Nat.le_of_lt_succ a.1.isLt)).op)))
    (hfinite : ∃ (k : ℕ) (W : Fin k → X.Etale) (j : ∀ i, W i ⟶ V),
      Nonempty (IsColimit (Cofan.mk V j)) ∧
        ∀ i, CompactSpace (W i).left ∧ QuasiSeparatedSpace (W i).left ∧
          LocallyOfFinitePresentation (W i).hom ∧ QuasiCompact (W i).hom ∧
            QuasiSeparated (W i).hom)
    (D : MatchingDegree S (Fin.last (n + 1))) :
    ∃ U' : TruncatedFiniteSplitEtaleHypercover X (n + 1),
      U'.simplicial = S ∧ U'.restrict n (Nat.le_succ n) = U := by
  rcases U with ⟨simp, N, inc, split, finite, oldM, oldπ, oldhn, oldhu, oldμ, oldhμ, oldhc⟩
  dsimp at hs
  subst simp
  let U : TruncatedFiniteSplitEtaleHypercover X n :=
    ⟨_, N, inc, split, finite, oldM, oldπ, oldhn, oldhu, oldμ, oldhμ, oldhc⟩
  let oldD (q : Fin (n + 1)) : MatchingDegree S q.castSucc := {
    M := oldM q
    π := fun Δ h θ ↦ oldπ q ⟨Δ.obj, (Nat.le_of_lt h).trans
      (Nat.le_of_lt_succ q.isLt)⟩ h θ
    naturality := by
      intro Δ Δ' h h' α θ
      exact oldhn q _ _ h h' (SimplexCategory.Truncated.Hom.tr α.hom _ _) θ
    universal := by
      intro T p hp
      let pold (Δ : SimplexCategory.Truncated n) (h : Δ.obj.len < q.val)
          (θ : Δ.obj ⟶ SimplexCategory.mk q.val) :=
        p ⟨Δ.obj, Δ.property.trans (Nat.le_succ _)⟩ h θ
      have hpold (Δ Δ' : SimplexCategory.Truncated n)
          (h : Δ.obj.len < q.val) (h' : Δ'.obj.len < q.val) (α : Δ' ⟶ Δ)
          (θ : Δ.obj ⟶ SimplexCategory.mk q.val) :
          pold Δ h θ ≫ (Scheme.Etale.forget X).map
            (((SimplicialObject.Truncated.trunc X.Etale (n + 1) n).obj S).map α.op) =
              pold Δ' h' (α.hom ≫ θ) := by
        exact hp _ _ h h' (SimplexCategory.Truncated.Hom.tr α.hom _ _) θ
      obtain ⟨f, hf, huniq⟩ := oldhu q T pold hpold
      refine ⟨f, ?_, ?_⟩
      · intro Δ h θ
        exact hf ⟨Δ.obj, (Nat.le_of_lt h).trans (Nat.le_of_lt_succ q.isLt)⟩ h θ
      · intro g hg
        apply huniq g
        intro Δ h θ
        exact hg ⟨Δ.obj, Δ.property.trans (Nat.le_succ _)⟩ h θ
    μ := oldμ q
    fac := fun Δ h θ ↦ oldhμ q
      ⟨Δ.obj, (Nat.le_of_lt h).trans (Nat.le_of_lt_succ q.isLt)⟩ h θ
    cover := oldhc q }
  let D' (q : Fin (n + 1 + 1)) : MatchingDegree S q := Fin.lastCases D oldD q
  have hsplit' (Δ : (SimplexCategory.Truncated (n + 1))ᵒᵖ) :
      IsColimit (Cofan.mk (S.obj Δ)
        (fun a : Σ m : Fin (n + 1 + 1),
          {α : Δ.unop.obj ⟶ SimplexCategory.mk m.val // Epi α} ↦
          (extNondeg U S rfl V ι a.1).inc ≫ S.map (SimplexCategory.Truncated.Hom.tr
            a.2.val Δ.unop.property (Nat.le_of_lt_succ a.1.isLt)).op)) := by
    by_cases hΔ : Δ.unop.obj.len ≤ n
    · let J (k : ℕ) := Σ m : Fin (k + 1),
          {α : Δ.unop.obj ⟶ SimplexCategory.mk m.val // Epi α}
      let e : J n ≃ J (n + 1) := {
        toFun := fun a ↦ ⟨a.1.castSucc, a.2⟩
        invFun := fun a ↦ ⟨⟨a.1.val, by
          have := a.2.property
          have he := SimplexCategory.len_le_of_epi a.2.val
          exact Nat.lt_succ_of_le (he.trans hΔ)⟩, a.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
      apply (Cofan.isColimitEquivOfEquiv e _).symm.toFun
      change IsColimit (Cofan.mk (S.obj Δ) (fun a : J n ↦
        (extNondeg U S rfl V ι a.1.castSucc).inc ≫
          S.map (SimplexCategory.Truncated.Hom.tr a.2.val Δ.unop.property
            (Nat.le_of_lt_succ a.1.castSucc.isLt)).op))
      have hN (a : J n) : (extNondeg U S rfl V ι a.1.castSucc).N = N a.1 := by
        rw [extNondeg, Fin.lastCases_castSucc]
      refine cofan_colimit_of_iso _ _ (fun a : J n ↦ eqToIso (hN a))
        (Iso.refl _) ?_ (split (op ⟨Δ.unop.obj, hΔ⟩))
      intro a
      change ((extNondeg U S rfl V ι a.1.castSucc).inc ≫ _) ≫ 𝟙 _ =
        eqToHom (hN a) ≫ inc a.1 ≫ _
      have hA : extNondeg U S rfl V ι a.1.castSucc =
          (⟨N a.1, inc a.1⟩ : NondegDegree S a.1.castSucc) := by
        rw [extNondeg, Fin.lastCases_castSucc]
        simp only [U, eqToHom_refl, Category.comp_id]
      rw [inc_of_eq hA]
      simp only [Category.assoc, Category.comp_id]
      rfl
    · have he : Δ = op ⟨SimplexCategory.mk (n + 1), le_rfl⟩ := by
        apply unop_injective
        apply ObjectProperty.FullSubcategory.ext
        apply SimplexCategory.ext
        have := Δ.unop.property
        dsimp
        omega
      subst Δ
      exact hsplit
  have hf' (q : Fin (n + 1 + 1)) : ∃ (k : ℕ) (W : Fin k → X.Etale)
      (j : ∀ i, W i ⟶ (extNondeg U S rfl V ι q).N),
      Nonempty (IsColimit (Cofan.mk (extNondeg U S rfl V ι q).N j)) ∧
        ∀ i, CompactSpace (W i).left ∧ QuasiSeparatedSpace (W i).left ∧
          LocallyOfFinitePresentation (W i).hom ∧ QuasiCompact (W i).hom ∧
            QuasiSeparated (W i).hom := by
    induction q using Fin.lastCases with
    | last =>
      rw [extNondeg, Fin.lastCases_last]
      exact hfinite
    | cast q =>
      rw [extNondeg, Fin.lastCases_castSucc]
      exact finite q
  let U' : TruncatedFiniteSplitEtaleHypercover X (n + 1) := {
    simplicial := S
    N := fun q ↦ (extNondeg U S rfl V ι q).N
    inclusion := fun q ↦ (extNondeg U S rfl V ι q).inc
    splitting := hsplit'
    finite_each_degree := hf'
    matching := fun q ↦ (D' q).M
    projection := fun q ↦ (D' q).π
    projection_naturality := fun q ↦ (D' q).naturality
    matching_universal := fun q ↦ (D' q).universal
    matchingMap := fun q ↦ (D' q).μ
    matchingMap_projection := fun q ↦ (D' q).fac
    matching_cover := fun q ↦ (D' q).cover }
  refine ⟨U', rfl, ?_⟩
  apply structure_ext (U'.restrict n (Nat.le_succ n)) U rfl
  · apply heq_of_eq
    funext q
    dsimp only [nondegOf, U', TruncatedFiniteSplitEtaleHypercover.restrict]
    rw [extNondeg, lastCases_mk]
    simp only [U, eqToHom_refl, Category.comp_id]
  · apply heq_of_eq
    funext q
    change lowerMatching S q (D' q.castSucc) = matchingOf U q
    rw [show D' q.castSucc = oldD q from Fin.lastCases_castSucc q]
    rfl

-- Uniqueness in the boundary universal property detects equality of maps over X.
private theorem boundary_hom_ext {X : Scheme.{u}} {n : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X n) (Q : ReplacementBoundary U)
    (T : Over X) (f g : T ⟶ (Scheme.Etale.forget X).obj Q.M)
    (h : ∀ (Δ : SimplexCategory.Truncated n)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)),
      f ≫ (Scheme.Etale.forget X).map (Q.π Δ θ) =
        g ≫ (Scheme.Etale.forget X).map (Q.π Δ θ)) : f = g := by
  let p Δ θ := g ≫ (Scheme.Etale.forget X).map (Q.π Δ θ)
  have hp (Δ Δ' : SimplexCategory.Truncated n) (α : Δ' ⟶ Δ)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)) :
      p Δ θ ≫ (Scheme.Etale.forget X).map (U.simplicial.map α.op) =
        p Δ' (α.hom ≫ θ) := by
    dsimp only [p]
    rw [Category.assoc, ← Functor.map_comp, Q.naturality]
  obtain ⟨t, ht, huniq⟩ := Q.universal T p hp
  exact (huniq f h).trans (huniq g (by intro Δ θ; rfl)).symm

-- The boundary determines the top matching map uniquely. Its restriction to V is b.
private theorem matching_top {X : Scheme.{u}} {n : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X n)
    (S : SimplicialObject.Truncated X.Etale (n + 1))
    (hs : (SimplicialObject.Truncated.trunc X.Etale (n + 1) n).obj S = U.simplicial)
    (V : X.Etale) (ι : V ⟶ S.obj (op ⟨SimplexCategory.mk (n + 1), le_rfl⟩))
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M) (hc : Surjective b.left)
    (hι : ∀ (Δ : SimplexCategory.Truncated n)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)),
      ι ≫ S.map (SimplexCategory.Truncated.Hom.tr θ
        (Δ.property.trans (Nat.le_succ n)) le_rfl).op =
        b ≫ Q.π Δ θ ≫ eqToHom (by rw [← hs]; rfl)) :
    Nonempty (MatchingDegree S (Fin.last (n + 1))) := by
  rcases U with ⟨simp, N, inc, split, finite, oldM, oldπ, oldhn, oldhu, oldμ, oldhμ, oldhc⟩
  dsimp at hs
  subst simp
  let U : TruncatedFiniteSplitEtaleHypercover X n :=
    ⟨_, N, inc, split, finite, oldM, oldπ, oldhn, oldhu, oldμ, oldhμ, oldhc⟩
  let p (Δ : SimplexCategory.Truncated n)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)) :=
    (Scheme.Etale.forget X).map (S.map
      (SimplexCategory.Truncated.Hom.tr θ (Δ.property.trans (Nat.le_succ n)) le_rfl).op)
  have hp (Δ Δ' : SimplexCategory.Truncated n) (α : Δ' ⟶ Δ)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)) :
      p Δ θ ≫ (Scheme.Etale.forget X).map (U.simplicial.map α.op) =
        p Δ' (α.hom ≫ θ) := by
    dsimp only [p, U]
    simp only [SimplicialObject.Truncated.trunc_obj_map]
    rw [← Functor.map_comp, ← S.map_comp]
    rfl
  obtain ⟨f, hf, huniq⟩ := Q.universal
    ((Scheme.Etale.forget X).obj (S.obj (op ⟨SimplexCategory.mk (n + 1), le_rfl⟩))) p hp
  let μ := (Scheme.Etale.forget X).preimage f
  have hμ (Δ : SimplexCategory.Truncated n)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)) :
      μ ≫ Q.π Δ θ = S.map (SimplexCategory.Truncated.Hom.tr θ
        (Δ.property.trans (Nat.le_succ n)) le_rfl).op := by
    apply (Scheme.Etale.forget X).map_injective
    simpa only [Functor.map_comp, μ, Functor.map_preimage] using hf Δ θ
  have he : ι ≫ μ = b := by
    apply (Scheme.Etale.forget X).map_injective
    apply boundary_hom_ext U Q
    intro Δ θ
    rw [← Functor.map_comp, Category.assoc, hμ]
    simpa only [eqToHom_refl, Category.comp_id, Functor.map_comp] using
      congrArg ((Scheme.Etale.forget X).map) (hι Δ θ)
  have hcover : Surjective μ.left := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := hc.surj y
    refine ⟨ι.left x, ?_⟩
    change (ι ≫ μ).left x = y
    rw [he]
    exact hx
  refine ⟨{
    M := Q.M
    π := fun Δ h θ ↦ Q.π ⟨Δ.obj, Nat.le_of_lt_succ h⟩ θ
    naturality := ?_
    universal := ?_
    μ := μ
    fac := ?_
    cover := hcover }⟩
  · intro Δ Δ' h h' α θ
    exact Q.naturality ⟨Δ.obj, Nat.le_of_lt_succ h⟩
      ⟨Δ'.obj, Nat.le_of_lt_succ h'⟩ (SimplexCategory.Truncated.Hom.tr α.hom _ _) θ
  · intro T p hp
    let pold (Δ : SimplexCategory.Truncated n)
        (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)) :=
      p ⟨Δ.obj, Δ.property.trans (Nat.le_succ n)⟩ (Nat.lt_succ_of_le Δ.property) θ
    have hpold (Δ Δ' : SimplexCategory.Truncated n) (α : Δ' ⟶ Δ)
        (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)) :
        pold Δ θ ≫ (Scheme.Etale.forget X).map (U.simplicial.map α.op) =
          pold Δ' (α.hom ≫ θ) :=
      hp _ _ _ _ (SimplexCategory.Truncated.Hom.tr α.hom _ _) θ
    obtain ⟨g, hg, huniq⟩ := Q.universal T pold hpold
    refine ⟨g, ?_, ?_⟩
    · intro Δ h θ
      exact hg ⟨Δ.obj, Nat.le_of_lt_succ h⟩ θ
    · intro g' hg'
      apply huniq g'
      intro Δ θ
      exact hg' ⟨Δ.obj, Δ.property.trans (Nat.le_succ n)⟩
        (Nat.lt_succ_of_le Δ.property) θ
  · intro Δ h θ
    exact hμ ⟨Δ.obj, Nat.le_of_lt_succ h⟩ θ

private theorem attachmentCoproducts {X : Scheme.{u}} {I : Type} :
     HasCoproductsOfShape I X.Etale := by
  dsimp [Scheme.Etale]
  infer_instance

private def newInclusion {X : Scheme.{u}} {n : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X n)
    (V : X.Etale) (Q : ReplacementBoundary U) (b : V ⟶ Q.M) :
    V ⟶ (attachedSimplicial U V Q b).obj
      (op ⟨SimplexCategory.mk (n + 1), le_rfl⟩) := by
  letI {I : Type} : HasCoproductsOfShape I X.Etale := attachmentCoproducts
  exact (coprod.inl : V ⟶ attachedFamily U V) ≫
    eqToHom (by simp [attachedSimplicial, attachmentTerm, attachedFamily])

-- The only epi endomorphism of the top simplex is its identity.
private def topLabels (n : ℕ) : Option (Labels n (n + 1)) ≃ Labels (n + 1) (n + 1) where
  toFun j := match j with
    | none => ⟨Fin.last (n + 1), ⟨𝟙 _, inferInstance⟩⟩
    | some a => ⟨a.1.castSucc, a.2⟩
  invFun a := if h : a.1.val < n + 1 then some ⟨⟨a.1.val, h⟩, a.2⟩ else none
  left_inv j := by
    cases j with
    | none => simp
    | some a => simp [a.1.isLt]
  right_inv a := by
    rcases a with ⟨q, σ, hσ⟩
    dsimp only
    split_ifs with hq
    · rfl
    · have he : q = Fin.last (n + 1) := Fin.ext (by have := q.isLt; dsimp; omega)
      subst q
      have hi : σ = 𝟙 _ := @SimplexCategory.eq_id_of_epi _ σ hσ
      subst σ
      rfl

private theorem inclusion_attachEpi {X : Scheme.{u}} {n : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (a : Labels n (n + 1)) :
    U.inclusion a.1 ≫ attachEpi U V a.1 a.2.val a.2.property = oldInclusion U V a := by
  have h := attachEpi_fac U V a.1 ⟨a.1, ⟨𝟙 _, inferInstance⟩⟩ a.2.val a.2.property
  have hi : oldInclusion U V
      (precomposeLabel ⟨a.1, ⟨𝟙 _, inferInstance⟩⟩ a.2.val a.2.property) =
      oldInclusion U V a := by
    dsimp only [precomposeLabel]
    congr 2
    apply Subtype.ext
    exact Category.comp_id _
  calc
    _ = oldInclusion U V
        (precomposeLabel ⟨a.1, ⟨𝟙 _, inferInstance⟩⟩ a.2.val a.2.property) := by
      have hid : operator U (𝟙 (SimplexCategory.mk a.1.val)) = 𝟙 (term U a.1) :=
        U.simplicial.map_id _
      simpa only [hid, Category.comp_id] using h
    _ = _ := hi

-- Separate the identity label from the old labels to recover the explicit coproduct.
private def splitting_top {X : Scheme.{u}} {n : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M) :
    IsColimit (Cofan.mk
      ((attachedSimplicial U V Q b).obj (op ⟨SimplexCategory.mk (n + 1), le_rfl⟩))
      (fun a : Labels (n + 1) (n + 1) ↦
        (extNondeg U (attachedSimplicial U V Q b)
          (attachedSimplicial_restrict U V Q b) V (newInclusion U V Q b) a.1).inc ≫
        (attachedSimplicial U V Q b).map (SimplexCategory.Truncated.Hom.tr
          a.2.val le_rfl (Nat.le_of_lt_succ a.1.isLt)).op)) := by
  letI {I : Type} : HasCoproductsOfShape I X.Etale := attachmentCoproducts
  let S := attachedSimplicial U V Q b
  let A := extNondeg U S (attachedSimplicial_restrict U V Q b) V (newInclusion U V Q b)
  let F : Option (Labels n (n + 1)) → X.Etale := fun j ↦ match j with
    | none => V
    | some a => U.N a.1
  let legs (j : Option (Labels n (n + 1))) : F j ⟶ attachedFamily U V :=
    match j with
    | none => coprod.inl
    | some a => oldInclusion U V a
  have hd : IsColimit (Cofan.mk (attachedFamily U V) legs) := by
    refine Cofan.IsColimit.mk _
      (fun s ↦ coprod.desc (show V ⟶ s.pt from s.inj none)
        (Sigma.desc (f := fun a : Labels n (n + 1) ↦ U.N a.1)
          (fun a ↦ s.inj (some a)))) ?_ ?_
    · intro s j
      cases j with
      | none => exact coprod.inl_desc _ _
      | some a => simp [legs, oldInclusion]
    · intro s m hm
      apply coprod.hom_ext
      · simpa [legs] using hm none
      · apply Sigma.hom_ext
        intro a
        simpa [legs, oldInclusion, Category.assoc] using hm (some a)
  let E (j : Option (Labels n (n + 1))) : (A ((topLabels n) j).1).N ≅ F j := by
    apply eqToIso
    cases j with
    | none =>
      dsimp only [A, topLabels, Equiv.coe_fn_mk]
      rw [extNondeg, Fin.lastCases_last]
    | some a =>
      dsimp only [A, topLabels, Equiv.coe_fn_mk]
      rw [extNondeg, Fin.lastCases_castSucc]
  have ht : S.obj (op ⟨SimplexCategory.mk (n + 1), le_rfl⟩) = attachedFamily U V := by
    simp [S, attachedSimplicial, attachmentTerm]
  apply (Cofan.isColimitEquivOfEquiv (topLabels n) _).symm.toFun
  refine cofan_colimit_of_iso _ (Cofan.mk (attachedFamily U V) legs) E
    (eqToIso ht) ?_ hd
  intro j
  cases j with
  | none =>
    have hA : A (Fin.last (n + 1)) =
        (⟨V, newInclusion U V Q b⟩ : NondegDegree S (Fin.last (n + 1))) :=
      Fin.lastCases_last
    change ((A (Fin.last (n + 1))).inc ≫ S.map
      (𝟙 (op (⟨SimplexCategory.mk (n + 1), le_rfl⟩ :
        SimplexCategory.Truncated (n + 1))))) ≫ eqToHom ht =
          eqToHom (congrArg NondegDegree.N hA) ≫
            (coprod.inl : V ⟶ attachedFamily U V)
    erw [S.map_id, Category.comp_id, inc_of_eq hA]
    simp only [newInclusion, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id]
  | some a =>
    have hlow : term U a.1 =
        attachmentTerm U V ⟨a.1.val, Nat.lt_succ_of_lt a.1.isLt⟩ := by
      simp only [attachmentTerm, dite_eq_left a.1.isLt]
    have hA : A a.1.castSucc =
        (⟨U.N a.1, U.inclusion a.1 ≫ eqToHom hlow⟩ :
            NondegDegree S a.1.castSucc) := Fin.lastCases_castSucc a.1
    change ((A a.1.castSucc).inc ≫ attachmentMap U V Q b
      ⟨n + 1, Nat.lt_succ_self _⟩ ⟨a.1.val, Nat.lt_succ_of_lt a.1.isLt⟩
        a.2.val) ≫ eqToHom ht =
          eqToHom (congrArg NondegDegree.N hA) ≫ oldInclusion U V a
    rw [inc_of_eq hA, attachmentMap_epi U V Q b a.1 a.2.val a.2.property]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp, Category.comp_id]
    change eqToHom (congrArg NondegDegree.N hA) ≫ U.inclusion a.1 ≫
      attachEpi U V a.1 a.2.val a.2.property =
        eqToHom (congrArg NondegDegree.N hA) ≫ oldInclusion U V a
    rw [inclusion_attachEpi]

/-- Source: Stacks, Hypercoverings, 0DAV, split extension; 01GJ, matching covers.

Use the old nondegenerate schemes and inclusions below the new degree, and use
V with the left coproduct injection in the top degree. In a lower degree every
epi has target degree at most that degree; remove the impossible top labels and
use U.splitting. In the top degree an epi to itself is the identity. Separate
this unique new label from all labels of target degree at most n. Their cofan
is the binary coproduct of V and the coproduct indexed by Labels n (n+1).
The identity label gives coprod.inl. For each lower label, attachmentMap_epi
and attachEpi_fac with the identity old label give exactly oldInclusion.
Therefore the canonical coproduct colimit proves the top splitting cofan.

Keep each old matching scheme, projection and matching map. The new matching
scheme is Q.M. Every simplex of degree below n+1 lies in the old truncation,
so Q.pi gives all its projections; Q.naturality gives their equations. Its
universal property is Q.universal, after transporting along the old restriction
of attachedSimplicial. Apply that universal property to the cone of top face
operators attachFace to define the matching map. This cone is natural by
attachFace_naturality. Uniqueness in Q.universal, after precomposing with the
new inclusion coprod.inl, identifies its restriction with b. Since b is
surjective, the matching map is surjective. This choice is determined uniquely
by all projections, not an arbitrary witness of mere existence.

Use hf for the new nondegenerate finiteness witness and retain every old witness.
Every lower field is literally retained; the proved restriction identity of
attachedSimplicial identifies the simplicial fields. Dependent structure
extensionality, uniqueness of colimit witnesses, and proof irrelevance for
proposition-valued fields yield the exact restriction equality stated below.
This theorem has no refinement target K:
the simplicial object and all its operator laws are already constructed.
(auxiliary; not a blueprint node) -/
theorem exists_attached_split_structure
    {X : Scheme.{u}} {n : ℕ} (U : TruncatedFiniteSplitEtaleHypercover X n)
    (V : X.Etale) (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (hc : Surjective b.left)
    (hf : ∃ (k : ℕ) (W : Fin k → X.Etale) (ι : ∀ i, W i ⟶ V),
      Nonempty (IsColimit (Cofan.mk V ι)) ∧
        ∀ i, CompactSpace (W i).left ∧ QuasiSeparatedSpace (W i).left ∧
          LocallyOfFinitePresentation (W i).hom ∧ QuasiCompact (W i).hom ∧
            QuasiSeparated (W i).hom) :
    ∃ U' : TruncatedFiniteSplitEtaleHypercover X (n + 1),
      U'.simplicial = attachedSimplicial U V Q b ∧
        U'.restrict n (Nat.le_succ n) = U := by
  classical
  let S := attachedSimplicial U V Q b
  let ι := newInclusion U V Q b
  have hι (Δ : SimplexCategory.Truncated n)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)) :
      ι ≫ S.map (SimplexCategory.Truncated.Hom.tr θ
        (Δ.property.trans (Nat.le_succ n)) le_rfl).op =
        b ≫ Q.π Δ θ ≫ eqToHom (by
          rw [← attachedSimplicial_restrict U V Q b]; rfl) := by
    simp [ι, S, newInclusion, attachedSimplicial, attachmentMap, attachmentTerm,
      Nat.lt_succ_of_le Δ.property, attachFace, Category.assoc]
  obtain ⟨D⟩ := matching_top U S (attachedSimplicial_restrict U V Q b) V ι Q b hc hι
  exact extend_structure U S (attachedSimplicial_restrict U V Q b) V ι
    (splitting_top U V Q b) hf D

end AlgebraicGeometry.SchemeSplitAttachment
