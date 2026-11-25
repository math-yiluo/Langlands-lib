/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends

/-!
# A nontrivial partition invariant over a finite intermediate field

Source: Stacks Project, Varieties, Tag 0389, proof, paragraphs 2--5, and the
pullback identification in its last paragraph.
(blueprint: lem-weil-pbc-galois-finite-invariant-clopen-partition).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem orbit_intersection
    {G S B : Type*} [Group G] [TopologicalSpace S] [TopologicalSpace B]
    (a : G → S ≃ₜ S) (p : S → B) (hpcont : Continuous p)
    (h1 : ∀ x, a 1 x = x)
    (hmul : ∀ g h x, a (g * h) x = a h (a g x))
    (hp : ∀ g x, p (a g x) = p x)
    (U : Set S) (hU : IsClopen U)
    (hlocal : ∀ x : B, ∃ W : Set B, x ∈ W ∧ IsOpen W ∧
      (Set.range fun g : G ↦ a g '' (p ⁻¹' W ∩ U)).Finite)
    (A : Set S) (hAne : A.Nonempty) (hAU : A ⊆ U)
    (hAinv : ∀ g, a g '' A = A) (hUc : Uᶜ.Nonempty) :
    ∃ V : Set S, IsClopen V ∧ V.Nonempty ∧ Vᶜ.Nonempty ∧
      ∀ g, a g '' V = V := by
  let V : Set S := ⋂ g : G, a g '' U
  have himage (g : G) (W : Set B) :
      a g '' (p ⁻¹' W ∩ U) = p ⁻¹' W ∩ (a g '' U) := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyW, hyU⟩, rfl⟩
      exact ⟨by simpa only [Set.mem_preimage, hp] using hyW, ⟨y, hyU, rfl⟩⟩
    · rintro ⟨hxW, y, hyU, rfl⟩
      exact ⟨y, ⟨by simpa only [Set.mem_preimage, hp] using hxW, hyU⟩, rfl⟩
  have hclosed : IsClosed V := isClosed_iInter fun g ↦
    (a g).isClosedMap U hU.isClosed
  have hopen : IsOpen V := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨W, hxW, hW, hfin⟩ := hlocal (p x)
    let F := Set.range fun g : G ↦ a g '' (p ⁻¹' W ∩ U)
    have hFopen : ∀ C ∈ F, IsOpen C := by
      rintro C ⟨g, rfl⟩
      exact (a g).isOpenMap _ ((hW.preimage hpcont).inter hU.isOpen)
    have hlocopen : IsOpen (⋂₀ F) := hfin.isOpen_sInter hFopen
    have hloc : ⋂₀ F = p ⁻¹' W ∩ V := by
      ext y
      simp only [Set.mem_sInter, F, Set.forall_mem_range, himage,
        Set.mem_inter_iff, V, Set.mem_iInter]
      constructor
      · intro hy
        exact ⟨(hy 1).1, fun g ↦ (hy g).2⟩
      · rintro ⟨hyW, hyV⟩ g
        exact ⟨hyW, hyV g⟩
    refine ⟨⋂₀ F, ?_, hlocopen, ?_⟩
    · rw [hloc]
      exact Set.inter_subset_right
    · rw [hloc]
      exact ⟨hxW, hx⟩
  have hsub : V ⊆ U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iInter.mp hx 1
    rw [h1] at hxy
    exact hxy ▸ hy
  have hAsub : A ⊆ V := by
    intro x hx
    apply Set.mem_iInter.mpr
    intro g
    have hx' : x ∈ a g '' A := by rw [hAinv g]; exact hx
    exact Set.image_mono hAU hx'
  refine ⟨V, ⟨hclosed, hopen⟩, hAne.mono hAsub, hUc.mono ?_, ?_⟩
  · exact Set.compl_subset_compl.mpr hsub
  · intro g
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      apply Set.mem_iInter.mpr
      intro h
      obtain ⟨z, hz, hzy⟩ := Set.mem_iInter.mp hy (h * g⁻¹)
      refine ⟨z, hz, ?_⟩
      rw [← hzy, ← hmul]
      simp
    · intro hx
      refine ⟨(a g).symm x, ?_, by simp⟩
      apply Set.mem_iInter.mpr
      intro h
      obtain ⟨z, hz, hzx⟩ := Set.mem_iInter.mp hx (h * g)
      refine ⟨z, hz, ?_⟩
      apply (a g).injective
      rw [← hmul, hzx]
      simp


/-- A nontrivial clopen partition after a Galois extension can be replaced by a
nontrivial partition invariant under the automorphisms over a finite intermediate field.
The partition is expressed on the iterated base change over that intermediate field.

Source: Stacks Project, Varieties, Lemma Tag 0389
(blueprint: lem-weil-pbc-galois-finite-invariant-clopen-partition).

Proof: Write p : X_L → X and let U and its complement be the given partition.
For every quasi-compact open W of X, p⁻¹(W) is quasi-compact because p is the base
change of a morphism of affine schemes. Its intersections with U and Uᶜ are
quasi-compact opens, since they are closed in p⁻¹(W). Apply Tag 04KU to descend
p⁻¹(W) ∩ U to a finite intermediate field K_W; the automorphisms fixing K_W
also preserve its complement inside p⁻¹(W). Choose u ∈ U and an affine open W₀
containing p(u), and set K = K_W₀ and H = Aut(L/K).
For every W, the H-translates of p⁻¹(W) ∩ U form a finite family: two
translates agree when the inverses of their automorphisms have the same
restriction to K_W, and a finite extension has finitely many embeddings into L.
Set U_W to their intersection and V_W to the union of the corresponding
translates of p⁻¹(W) ∩ Uᶜ. These are complementary clopen subsets of p⁻¹(W),
and reindexing H proves their invariance. Restriction from W' to W ⊆ W'
commutes with these intersections and unions because every automorphism fixes
p⁻¹(W). Applying this to W ∪ W' proves compatibility for arbitrary W, W'.
Their unions over all quasi-compact W therefore form a complementary open,
hence clopen, partition of X_L. The first part contains u because the
partition on W₀ is already H-invariant; the second contains Uᶜ because the
identity automorphism is among the translates. Thus both parts are nonempty.
Finally use pullback pasting to identify X_L with (X_K)_L. Its universal
property identifies the H-action with the base-change action over K, so the
transported first part has all the asserted properties. No compactness or
quasi-separatedness assumption on X is needed: only the opens W are compact. -/
theorem exists_finite_invariant_clopen_partition
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (U : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))))
    (hU : IsClopen U) (hne : U.Nonempty) (hne' : Uᶜ.Nonempty) :
    ∃ K : IntermediateField k L, FiniteDimensional k K ∧
      ∃ V : Set ↥(pullback
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Spec.map (CommRingCat.ofHom (algebraMap K L)))),
        IsClopen V ∧ V.Nonempty ∧ Vᶜ.Nonempty ∧
          ∀ σ : L ≃ₐ[K] L,
            (baseChangeMap
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
              (specAlgEquivOver σ)) '' V = V := by
  classical
  let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let Z := pullback f g
  let p := pullback.fst f g
  let σX := fun σ : L ≃ₐ[k] L ↦ baseChangeMap f (specAlgEquivOver σ)
  obtain ⟨hiso, hcomp, -⟩ :=
    galois_baseChange_qc_open_descends k L X f ⊥ isCompact_empty
  let a : (L ≃ₐ[k] L) → Z ≃ₜ Z := fun σ ↦
    have := hiso σ
    (σX σ).homeomorph
  have ha (σ : L ≃ₐ[k] L) (x : Z) : a σ x = σX σ x :=
    Scheme.Hom.homeomorph_apply _ _
  have h1 : ∀ x, a 1 x = x := by
    have he : specAlgEquivOver (1 : L ≃ₐ[k] L) = 𝟙 _ := by
      apply Over.OverMorphism.ext
      change Spec.map (CommRingCat.ofHom (RingHom.id L)) = 𝟙 _
      exact Spec.map_id _
    intro x
    simp only [ha, σX, he, baseChangeMap_id]
    rfl
  have hmul (σ τ : L ≃ₐ[k] L) (x : Z) : a (σ * τ) x = a τ (a σ x) := by
    simp only [ha]
    change (σX (σ * τ)) x = (σX τ) ((σX σ) x)
    rw [show σX (σ * τ) = σX σ ≫ σX τ from hcomp σ τ]
    exact Scheme.Hom.comp_apply _ _ _
  have hp (σ : L ≃ₐ[k] L) (x : Z) : p (a σ x) = p x := by
    simpa only [ha, σX, p, g, Scheme.Hom.comp_apply, Over.mk_hom] using
      congrArg (fun q : Z ⟶ X ↦ q x) (baseChangeMap_fst f (specAlgEquivOver σ))
  have hcompact (W : X.Opens) (hW : IsAffineOpen W) : IsCompact (p ⁻¹' W.1 ∩ U) := by
    have : QuasiCompact g := inferInstance
    exact (QuasiCompact.isCompact_preimage (f := p) W.1 W.2 hW.isCompact).inter_right hU.isClosed
  have hfinite (W : X.Opens) (hW : IsAffineOpen W) :
      (Set.range fun σ : L ≃ₐ[k] L ↦ a σ '' (p ⁻¹' W.1 ∩ U)).Finite := by
    let A : Z.Opens := ⟨p ⁻¹' W.1 ∩ U, (W.2.preimage p.continuous).inter hU.isOpen⟩
    obtain ⟨-, -, E, hE, -, -, -, -, -, hfix⟩ :=
      galois_baseChange_qc_open_descends k L X f A (hcompact W hW)
    have := hE
    let res : (L ≃ₐ[k] L) → (E →ₐ[k] L) :=
      fun σ ↦ σ.symm.toAlgHom.comp E.val
    have hfactor : Function.FactorsThrough (fun σ : L ≃ₐ[k] L ↦ a σ '' A.1) res := by
      intro σ τ heq
      let ρ : L ≃ₐ[k] L := τ * σ⁻¹
      have hρ : ∀ x : E, ρ (x : L) = (x : L) := by
        intro x
        have hx := congrArg (fun b : E →ₐ[k] L ↦ b x) heq
        change σ.symm (x : L) = τ.symm (x : L) at hx
        change τ (σ.symm (x : L)) = (x : L)
        rw [hx, AlgEquiv.apply_symm_apply]
      have hρA : a ρ '' A.1 = A.1 := by
        simpa only [Set.image, ha, σX, Z, g, Over.mk_hom] using hfix ρ hρ
      have hτσ : τ = ρ * σ := by simp [ρ]
      have him : a τ '' A.1 = a σ '' (a ρ '' A.1) := by
        rw [Set.image_image, hτσ]
        congr 1
        funext x
        exact hmul ρ σ x
      change a σ '' A.1 = a τ '' A.1
      rw [him, hρA]
    obtain ⟨b, hb⟩ := (Function.factorsThrough_iff _).mp hfactor
    rw [hb]
    exact (Set.finite_range b).subset (Set.range_comp_subset_range _ _)
  obtain ⟨u, hu⟩ := hne
  obtain ⟨W₀, hW₀, huW₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := p u) (U := ⊤) trivial
  let A : Z.Opens := ⟨p ⁻¹' W₀.1 ∩ U, (W₀.2.preimage p.continuous).inter hU.isOpen⟩
  obtain ⟨-, -, K, hK, -, -, -, -, -, hfix⟩ :=
    galois_baseChange_qc_open_descends k L X f A (hcompact W₀ hW₀)
  have := hK
  let b : (L ≃ₐ[K] L) → Z ≃ₜ Z := fun σ ↦ a (σ.restrictScalars k)
  have hb1 : ∀ x, b 1 x = x := by
    intro x
    simpa only [b, ← AlgEquiv.restrictScalarsHom_apply, map_one] using h1 x
  have hbmul (σ τ : L ≃ₐ[K] L) (x : Z) : b (σ * τ) x = b τ (b σ x) := by
    simpa only [b, ← AlgEquiv.restrictScalarsHom_apply, map_mul] using
      hmul (σ.restrictScalars k) (τ.restrictScalars k) x
  have hbp (σ : L ≃ₐ[K] L) (x : Z) : p (b σ x) = p x := hp _ x
  have hlocal (x : X) : ∃ W : Set X, x ∈ W ∧ IsOpen W ∧
      (Set.range fun σ : L ≃ₐ[K] L ↦ b σ '' (p ⁻¹' W ∩ U)).Finite := by
    obtain ⟨W, hW, hxW, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
    refine ⟨W.1, hxW, W.2, (hfinite W hW).subset ?_⟩
    rintro C ⟨σ, rfl⟩
    exact ⟨σ.restrictScalars k, rfl⟩
  have hAinv (σ : L ≃ₐ[K] L) : b σ '' A.1 = A.1 := by
    have hs : ∀ x : K, (σ.restrictScalars k) (x : L) = (x : L) := by
      intro x
      exact σ.commutes x
    simpa only [b, Set.image, ha, σX, Z, g, Over.mk_hom] using hfix _ hs
  obtain ⟨V, hV, hVne, hVcne, hVinv⟩ := orbit_intersection b p p.continuous hb1 hbmul
    hbp U hU hlocal A.1 ⟨u, huW₀, hu⟩ Set.inter_subset_right hAinv hne'
  let gK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let gL := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have heq : gL ≫ gK = g := by
    simp only [gL, gK, g, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
  let e : pullback (pullback.snd f gK) gL ≅ Z :=
    pullbackLeftPullbackSndIso f gK gL ≪≫ pullback.congrHom rfl heq
  have hefst : e.hom ≫ pullback.fst f g =
      pullback.fst (pullback.snd f gK) gL ≫ pullback.fst f gK := by
    simp [e]
  have hesnd : e.hom ≫ pullback.snd f g = pullback.snd (pullback.snd f gK) gL := by
    simp [e]
  have haction (σ : L ≃ₐ[K] L) :
      baseChangeMap (pullback.snd f gK) (specAlgEquivOver σ) ≫ e.hom =
        e.hom ≫ σX (σ.restrictScalars k) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hefst, σX]
      simp only [baseChangeMap, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.comp_id,
        gL, g, gK, Over.mk_hom]
      simpa only [gL, gK, g] using hefst.symm
    · simp only [Category.assoc, hesnd, σX]
      simp only [baseChangeMap, pullback.map, pullback.lift_snd,
        gL, g, gK, Over.mk_hom]
      rw [← Category.assoc, hesnd]
      rfl
  let V' : Set ↥(pullback (pullback.snd f gK) gL) := e.hom ⁻¹' V
  have hV'ne : V'.Nonempty := by
    obtain ⟨v, hv⟩ := hVne
    obtain ⟨w, hw⟩ := e.hom.homeomorph.surjective v
    refine ⟨w, ?_⟩
    change e.hom w ∈ V
    simpa only [Scheme.Hom.homeomorph_apply] using hw ▸ hv
  have hVc'ne : V'ᶜ.Nonempty := by
    obtain ⟨v, hv⟩ := hVcne
    obtain ⟨w, hw⟩ := e.hom.homeomorph.surjective v
    refine ⟨w, ?_⟩
    change e.hom w ∉ V
    simpa only [Scheme.Hom.homeomorph_apply] using hw ▸ hv
  refine ⟨K, hK, V', hV.preimage e.hom.continuous, hV'ne, hVc'ne, ?_⟩
  intro σ
  let q := baseChangeMap (pullback.snd f gK) (specAlgEquivOver σ)
  have hq (x) : e.hom (q x) = b σ (e.hom x) := by
    simpa only [Scheme.Hom.comp_apply, b, ha, q, gK, Over.mk_hom] using
      congrArg (fun t ↦ t x) (haction σ)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change e.hom (q y) ∈ V
    rw [hq]
    rw [← hVinv σ]
    exact ⟨e.hom y, hy, rfl⟩
  · intro hx
    have hx' : e.hom x ∈ b σ '' V := by
      rw [hVinv σ]
      exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    obtain ⟨z, hz⟩ := e.hom.homeomorph.surjective y
    have hz' : e.hom z = y := by simpa only [Scheme.Hom.homeomorph_apply] using hz
    refine ⟨z, ?_, ?_⟩
    · change e.hom z ∈ V
      rw [hz']
      exact hy
    · apply e.hom.homeomorph.injective
      simp only [Scheme.Hom.homeomorph_apply]
      change e.hom (q z) = e.hom x
      rw [hq, hz']
      exact hyx

end AlgebraicGeometry
