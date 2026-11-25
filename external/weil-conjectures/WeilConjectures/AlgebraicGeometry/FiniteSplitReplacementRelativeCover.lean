/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStage
public import WeilConjectures.AlgebraicGeometry.EtaleHypercover
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.LimitsOver
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! Finite affine covers of relative boundary schemes. -/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Source: Stacks Project, Hypercoverings, 01GJ, relative matching construction,
and 094K, finite affine choices.

Compose the boundary projections with A.f and use the universal matching property
of K to obtain M(A) to M(K). Pull back the surjective etale arrow K_(n+1) to M(K).
Its projection to M(A) is still surjective and etale. Its affine opens have open
images covering the compact space M(A), so finitely many suffice. Take their
finite disjoint union N and its two maps b to M(A) and g to K_(n+1). The pullback
equation and K's matching projection equations prove compatibility with every
lower face. The chosen pieces are affine, hence qcqs; their etale structure maps
to the qcqs base X are locally of finite presentation, quasi-compact and
quasi-separated. This uses no compactness hypothesis on any term of K.
(auxiliary; not a blueprint node) -/
theorem exists_finite_relative_boundary_cover
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject X.Etale) (hK : IsEtaleHypercover K)
    {n : ℕ} (A : FiniteSplitReplacementStage K n) (Q : ReplacementBoundary A.U) :
    ∃ (N : X.Etale) (b : N ⟶ Q.M) (g : N ⟶ K.obj (op (SimplexCategory.mk (n + 1)))),
      Surjective b.left ∧
      (∃ (k : ℕ) (V : Fin k → X.Etale) (ι : ∀ i, V i ⟶ N),
        Nonempty (IsColimit (Cofan.mk N ι)) ∧
          ∀ i, CompactSpace (V i).left ∧ QuasiSeparatedSpace (V i).left ∧
            LocallyOfFinitePresentation (V i).hom ∧ QuasiCompact (V i).hom ∧
              QuasiSeparated (V i).hom) ∧
      ∀ (Δ : SimplexCategory.Truncated n) (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)),
        b ≫ Q.π Δ θ ≫ A.f.app (op Δ) = g ≫ K.map θ.op := by
  classical
  let : CompactSpace Q.M.left := Q.compact
  let : QuasiSeparatedSpace Q.M.left := Q.quasiSeparated
  obtain ⟨MK, πK, μK, hn, hu, hp, hc⟩ := hK (n + 1)
  let p (Δ : SimplexCategory) (h : Δ.len < n + 1)
      (θ : Δ ⟶ SimplexCategory.mk (n + 1)) :=
    (Scheme.Etale.forget X).map
      (Q.π ⟨Δ, Nat.le_of_lt_succ h⟩ θ ≫ A.f.app (op ⟨Δ, Nat.le_of_lt_succ h⟩))
  have hpn : ∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n + 1) (h' : Δ'.len < n + 1)
      (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk (n + 1)),
      p Δ h θ ≫ (Scheme.Etale.forget X).map (K.map α.op) = p Δ' h' (α ≫ θ) := by
    intro Δ Δ' h h' α θ
    dsimp [p]
    rw [← Functor.map_comp]
    congr 1
    have ha := A.f.naturality (SimplexCategory.Truncated.Hom.tr α
      (Nat.le_of_lt_succ h') (Nat.le_of_lt_succ h)).op
    change A.U.simplicial.map (SimplexCategory.Truncated.Hom.tr α _ _).op ≫
      A.f.app (op ⟨Δ', Nat.le_of_lt_succ h'⟩) =
        A.f.app (op ⟨Δ, Nat.le_of_lt_succ h⟩) ≫ K.map α.op at ha
    rw [Category.assoc, ← ha, ← Category.assoc, Q.naturality]
    rfl
  obtain ⟨t', ht, _⟩ := hu ((Scheme.Etale.forget X).obj Q.M) p hpn
  let t : Q.M ⟶ MK := MorphismProperty.Over.homMk t'.left (Over.w t') trivial
  have htf (Δ : SimplexCategory.Truncated n)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)) :
      t ≫ πK Δ.obj (Nat.lt_succ_of_le Δ.property) θ =
        Q.π Δ θ ≫ A.f.app (op Δ) := by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun f ↦ f.left) (ht Δ.obj (Nat.lt_succ_of_le Δ.property) θ)
  let E : X.Etale := Scheme.Etale.mk (pullback.fst t.left μK.left ≫ Q.M.hom)
  let e : E ⟶ Q.M := MorphismProperty.Over.homMk (pullback.fst t.left μK.left) rfl trivial
  let gE : E ⟶ K.obj (op (SimplexCategory.mk (n + 1))) :=
    MorphismProperty.Over.homMk (pullback.snd t.left μK.left) (by
      rw [← MorphismProperty.Over.w μK, ← Category.assoc, ← pullback.condition,
        Category.assoc, MorphismProperty.Over.w t]
      rfl) trivial
  have heq : e ≫ t = gE ≫ μK := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.condition
  have hrel (Δ : SimplexCategory.Truncated n)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)) :
      e ≫ Q.π Δ θ ≫ A.f.app (op Δ) = gE ≫ K.map θ.op := by
    rw [← htf, ← Category.assoc, heq, Category.assoc, hp]
  let : Surjective μK.left := hc
  have : Surjective e.left := by
    change Surjective (pullback.fst t.left μK.left)
    infer_instance
  let C : Scheme.Cover.{0} (Scheme.precoverage @Etale) Q.M.left :=
    e.left.cover (P := @Etale) inferInstance
  have : QuasiCompactCover C.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun i ↦ (C.f i).isOpenMap)
  obtain ⟨k, a, V, hV, hcover⟩ :=
    QuasiCompactCover.exists_isAffineOpen_of_isCompact C.toPreZeroHypercover
      (show IsCompact (⊤ : Q.M.left.Opens).carrier from isCompact_univ)
  let W (i : Fin k) : X.Etale := Scheme.Etale.mk ((hV i).fromSpec ≫ E.hom)
  let τ (i : Fin k) : W i ⟶ E :=
    MorphismProperty.Over.homMk (hV i).fromSpec rfl trivial
  have : HasCoproductsOfShape (Fin k) X.Etale := by dsimp [Scheme.Etale]; infer_instance
  let N := ∐ W
  let ν : N ⟶ E := Sigma.desc τ
  have hsurj : Surjective (ν ≫ e).left := by
    constructor
    intro x
    have hx : x ∈ ⋃ i, C.f (a i) '' (V i : Set (C.X (a i))) := by
      rw [hcover]
      trivial
    simp only [Set.mem_iUnion, Set.mem_image] at hx
    obtain ⟨i, y, hy, hxy⟩ := hx
    obtain ⟨z, hz⟩ : ∃ z, (hV i).fromSpec z = y := by
      change y ∈ Set.range (hV i).fromSpec
      rw [(hV i).range_fromSpec]
      exact hy
    refine ⟨(Sigma.ι W i).left z, ?_⟩
    have hw : (Sigma.ι W i).left ≫ (ν ≫ e).left = (τ i ≫ e).left :=
      congrArg (fun f ↦ f.left) (Sigma.ι_comp_desc_assoc τ i e)
    change ((Sigma.ι W i).left ≫ (ν ≫ e).left) z = x
    rw [hw]
    change e.left ((hV i).fromSpec z) = x
    rw [hz]
    exact hxy
  refine ⟨N, ν ≫ e, ν ≫ gE, hsurj, ?_, ?_⟩
  · refine ⟨k, W, Sigma.ι W, ⟨coproductIsCoproduct W⟩, ?_⟩
    intro i
    have hcompact : CompactSpace (W i).left := by
      change CompactSpace (Spec Γ(C.X (a i), V i))
      infer_instance
    have hqs : QuasiSeparatedSpace (W i).left := by
      change QuasiSeparatedSpace (Spec Γ(C.X (a i), V i))
      infer_instance
    refine ⟨hcompact, hqs, inferInstance, ?_, ?_⟩
    · exact @quasiCompact_of_compactSpace _ X _ hcompact inferInstance
    · exact @QuasiSeparated.of_quasiSeparatedSpace _ _ _ hqs
  · intro Δ θ
    simp only [Category.assoc]
    exact congrArg (fun f ↦ ν ≫ f) (hrel Δ θ)

end AlgebraicGeometry
