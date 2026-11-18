import Langlands.GroupScheme.Torus.MultiplicativeTypeTrivialLocusClosedStatement
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Langlands.GroupScheme.Torus.CentralRigidityReduction
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-! # Proof: the trivial locus of a homomorphism from a group of multiplicative type is closed -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace MultiplicativeTypeTrivialLocusClosedProof

/-- For a free `B`-module `A` with basis `bA` and a `B`-algebra `C`, an element `a ⊗ 1` of
`A ⊗[B] C` vanishes exactly when every coordinate of `a` maps to zero in `C`. -/
private theorem tmul_one_eq_zero_iff {B C A I : Type u} [CommRing B] [CommRing C]
    [Algebra B C] [AddCommGroup A] [Module B A] (bA : Module.Basis I B A) (a : A) :
    a ⊗ₜ[B] (1 : C) = 0 ↔ ∀ i, algebraMap B C (bA.repr a i) = 0 := by
  classical
  let E : A ⊗[B] C ≃ₗ[B] (I →₀ C) :=
    (LinearEquiv.rTensor C bA.repr).trans (finsuppScalarLeft B C I)
  have hE : ∀ i, E (a ⊗ₜ[B] (1 : C)) i = algebraMap B C (bA.repr a i) := by
    intro i
    simp [E, Algebra.algebraMap_eq_smul_one]
  constructor
  · intro h i
    rw [← hE, h, map_zero, Finsupp.zero_apply]
  · intro h
    apply E.injective
    rw [map_zero]
    ext i
    rw [hE, h, Finsupp.zero_apply]

/-- Two morphisms `a b : X ⟶ Y` over a separated `Y ⟶ S` agree after precomposition with
`g : T ⟶ X` exactly when `g` contains the kernel of the closed immersion of their
equalizer (the pullback of the diagonal of `Y`). -/
private theorem comp_eq_iff_ker_le {X Y S T : Scheme.{u}} (π : Y ⟶ S) [IsSeparated π]
    (a b : X ⟶ Y) (h : a ≫ π = b ≫ π) (g : T ⟶ X) :
    g ≫ a = g ≫ b ↔
      (pullback.snd (pullback.diagonal π) (pullback.lift a b h)).ker ≤ g.ker := by
  constructor
  · intro hg
    let l : T ⟶ pullback (pullback.diagonal π) (pullback.lift a b h) :=
      pullback.lift (g ≫ a) g (by
        apply pullback.hom_ext
        · simp [pullback.lift_fst]
        · simp [pullback.lift_snd, hg])
    have hl : l ≫ pullback.snd _ _ = g := pullback.lift_snd _ _ _
    rw [← hl]
    exact Scheme.Hom.le_ker_comp _ _
  · intro hle
    rw [← IsClosedImmersion.lift_fac _ g hle]
    have ha : pullback.snd (pullback.diagonal π) (pullback.lift a b h) ≫ a =
        pullback.fst (pullback.diagonal π) (pullback.lift a b h) := by
      have := congrArg (· ≫ pullback.fst π π)
        (pullback.condition (f := pullback.diagonal π) (g := pullback.lift a b h))
      simpa [pullback.lift_fst, pullback.lift_snd] using this.symm
    have hb : pullback.snd (pullback.diagonal π) (pullback.lift a b h) ≫ b =
        pullback.fst (pullback.diagonal π) (pullback.lift a b h) := by
      have := congrArg (· ≫ pullback.snd π π)
        (pullback.condition (f := pullback.diagonal π) (g := pullback.lift a b h))
      simpa [pullback.lift_fst, pullback.lift_snd] using this.symm
    rw [Category.assoc, Category.assoc, ha, hb]

/-- On an affine target, comparison of kernels of morphisms is comparison of the kernels of
their maps on global sections. -/
private theorem ker_le_iff_of_isAffine {X T T' : Scheme.{u}} [IsAffine X] (j : T ⟶ X) (g : T' ⟶ X) :
    j.ker ≤ g.ker ↔ RingHom.ker j.appTop.hom ≤ RingHom.ker g.appTop.hom := by
  rw [Scheme.ker_of_isAffine j, Scheme.ker_of_isAffine g,
    ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply,
    ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply]
  exact (Scheme.IdealSheafData.equivOfIsAffine (X := X)).symm.toOrderIso.le_iff_le

/-- The residue-field morphism of `Spec B` at `s` is `Spec` of a ring map whose kernel is the
prime ideal `s`. -/
private theorem fromSpecResidueField_preimage_eq_zero_iff {B : CommRingCat.{u}} (s : Spec B)
    (c : B) :
    (Spec.preimage ((Spec B).fromSpecResidueField s)).hom c = 0 ↔ c ∈ s.asIdeal := by
  set φ := Spec.preimage ((Spec B).fromSpecResidueField s)
  have hφ : Spec.map φ = (Spec B).fromSpecResidueField s := Spec.map_preimage _
  let p : Spec ((Spec B).residueField s) := IsLocalRing.closedPoint _
  have hp : Spec.map φ p = s := by
    rw [hφ]
    exact Scheme.fromSpecResidueField_apply s p
  rw [Spec.map_apply] at hp
  have hs : (s : PrimeSpectrum B).asIdeal = Ideal.comap φ.hom p.asIdeal := by
    rw [← PrimeSpectrum.comap_asIdeal, hp]
  rw [hs, Ideal.mem_comap]
  change _ ↔ φ.hom c ∈ IsLocalRing.maximalIdeal _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]

/-- The kernel of `(Spec.map ψ).appTop` in terms of `ψ`. -/
private theorem SpecMap_appTop_eq_zero_iff {R C : CommRingCat.{u}} (ψ : R ⟶ C) (c : Γ(Spec R, ⊤)) :
    (Spec.map ψ).appTop.hom c = 0 ↔ ψ.hom ((Scheme.ΓSpecIso R).hom.hom c) = 0 := by
  have h := congrArg (fun f => f.hom c) (Scheme.ΓSpecIso_naturality ψ)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  rw [← h]
  exact (map_eq_zero_iff _ (Scheme.ΓSpecIso C).commRingCatIsoToRingEquiv.injective).symm

section Locus

variable {X X' Y S S' T T' : Scheme.{u}}

/-- Agreement after base change along a composite `c ≫ t` is agreement after the iterated base
change. -/
private theorem fst_comp_eq_iff (p : X ⟶ S) (t : T ⟶ S) (c : T' ⟶ T) (x y : X ⟶ Y) :
    pullback.fst p (c ≫ t) ≫ x = pullback.fst p (c ≫ t) ≫ y ↔
      pullback.fst (pullback.snd p t) c ≫ pullback.fst p t ≫ x =
        pullback.fst (pullback.snd p t) c ≫ pullback.fst p t ≫ y := by
  rw [← cancel_epi (pullbackLeftPullbackSndIso p t c).hom,
    pullbackLeftPullbackSndIso_hom_fst_assoc, pullbackLeftPullbackSndIso_hom_fst_assoc]

/-- Agreement after base change along `t` is equivalent to agreement after base change along
`c ≫ t`, for `c` flat and surjective. -/
private theorem fst_eq_iff_comp (p : X ⟶ S) (t : T ⟶ S) (c : T' ⟶ T) [Flat c] [Surjective c]
    (x y : X ⟶ Y) :
    pullback.fst p t ≫ x = pullback.fst p t ≫ y ↔
      pullback.fst p (c ≫ t) ≫ x = pullback.fst p (c ≫ t) ≫ y := by
  rw [fst_comp_eq_iff]
  constructor
  · intro h
    rw [h]
  · intro h
    have : Epi (pullback.fst (pullback.snd p t) c) := Flat.epi_of_flat_of_surjective _
    exact (cancel_epi _).1 h

/-- Agreement after base change is unchanged by precomposition with an isomorphism of the
source. -/
private theorem fst_eq_iff_of_isIso (k : X' ⟶ X) [IsIso k] (p : X ⟶ S) (t : T ⟶ S) (x y : X ⟶ Y) :
    pullback.fst (k ≫ p) t ≫ k ≫ x = pullback.fst (k ≫ p) t ≫ k ≫ y ↔
      pullback.fst p t ≫ x = pullback.fst p t ≫ y := by
  rw [← cancel_epi (pullbackRightPullbackFstIso p t k).hom,
    pullbackRightPullbackFstIso_hom_fst_assoc, pullbackRightPullbackFstIso_hom_fst_assoc,
    pullback.condition_assoc, pullback.condition_assoc, cancel_epi]

/-- The preimage of the agreement locus along `g : S' ⟶ S` is the agreement locus of the base
change along `g`. -/
private theorem preimage_locus (p : X ⟶ S) (x y : X ⟶ Y) (g : S' ⟶ S) :
    g ⁻¹' {s : S | pullback.fst p (S.fromSpecResidueField s) ≫ x =
        pullback.fst p (S.fromSpecResidueField s) ≫ y} =
      {v : S' | pullback.fst (pullback.snd p g) (S'.fromSpecResidueField v) ≫
          pullback.fst p g ≫ x =
        pullback.fst (pullback.snd p g) (S'.fromSpecResidueField v) ≫
          pullback.fst p g ≫ y} := by
  ext v
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [← fst_comp_eq_iff, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have : Surjective (Spec.map (g.residueFieldMap v)) :=
    ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩
  exact fst_eq_iff_comp p _ (Spec.map (g.residueFieldMap v)) x y

/-- Closedness of the agreement locus can be checked on a jointly surjective family of open
maps. -/
private theorem isClosed_of_cover {J : Type*} {U : J → Scheme.{u}} (g : ∀ i, U i ⟶ S)
    (hopen : ∀ i, IsOpenMap (g i)) (hsurj : ∀ s : S, ∃ i v, g i v = s)
    (p : X ⟶ S) (x y : X ⟶ Y)
    (h : ∀ i, IsClosed {v : U i |
      pullback.fst (pullback.snd p (g i)) ((U i).fromSpecResidueField v) ≫
          pullback.fst p (g i) ≫ x =
        pullback.fst (pullback.snd p (g i)) ((U i).fromSpecResidueField v) ≫
          pullback.fst p (g i) ≫ y}) :
    IsClosed {s : S | pullback.fst p (S.fromSpecResidueField s) ≫ x =
        pullback.fst p (S.fromSpecResidueField s) ≫ y} := by
  set Z := {s : S | pullback.fst p (S.fromSpecResidueField s) ≫ x =
        pullback.fst p (S.fromSpecResidueField s) ≫ y} with hZ
  have hcompl : Zᶜ = ⋃ i, (g i) '' ((g i) ⁻¹' Z)ᶜ := by
    ext s
    constructor
    · intro hs
      obtain ⟨i, v, rfl⟩ := hsurj s
      exact Set.mem_iUnion.2 ⟨i, v, hs, rfl⟩
    · intro hs
      obtain ⟨i, v, hv, rfl⟩ := Set.mem_iUnion.1 hs
      exact hv
  rw [← isOpen_compl_iff, hcompl]
  refine isOpen_iUnion fun i => hopen i _ ?_
  rw [hZ, preimage_locus]
  exact (h i).isOpen_compl

/-- Closedness of the agreement locus is unchanged by an isomorphism of the source. -/
private theorem isClosed_locus_of_isIso (k : X' ⟶ X) [IsIso k] (p : X ⟶ S) (p₀ : X' ⟶ S)
    (hk : k ≫ p = p₀) (x y : X ⟶ Y)
    (h : IsClosed {s : S | pullback.fst p₀ (S.fromSpecResidueField s) ≫ k ≫ x =
        pullback.fst p₀ (S.fromSpecResidueField s) ≫ k ≫ y}) :
    IsClosed {s : S | pullback.fst p (S.fromSpecResidueField s) ≫ x =
        pullback.fst p (S.fromSpecResidueField s) ≫ y} := by
  subst hk
  have : {s : S | pullback.fst (k ≫ p) (S.fromSpecResidueField s) ≫ k ≫ x =
        pullback.fst (k ≫ p) (S.fromSpecResidueField s) ≫ k ≫ y} =
      {s : S | pullback.fst p (S.fromSpecResidueField s) ≫ x =
        pullback.fst p (S.fromSpecResidueField s) ≫ y} :=
    Set.ext fun s => fst_eq_iff_of_isIso k p _ x y
  rw [← this]
  exact h

end Locus

/-- The affine free case: for a `B`-algebra `A` that is free as a `B`-module, the agreement locus
of two morphisms `Spec A ⟶ Y` that agree over a separated base is closed in `Spec B`. -/
private theorem isClosed_core {B A I : Type u} [CommRing B] [CommRing A] [Algebra B A]
    (bA : Module.Basis I B A) {Y S₀ : Scheme.{u}} (π : Y ⟶ S₀) [IsSeparated π]
    (x y : Spec (CommRingCat.of A) ⟶ Y) (h : x ≫ π = y ≫ π) :
    IsClosed {s : Spec (CommRingCat.of B) |
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B A)))
          ((Spec (CommRingCat.of B)).fromSpecResidueField s) ≫ x =
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B A)))
          ((Spec (CommRingCat.of B)).fromSpecResidueField s) ≫ y} := by
  let j := pullback.snd (pullback.diagonal π) (pullback.lift x y h)
  have key : ∀ s : Spec (CommRingCat.of B),
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B A)))
          ((Spec (CommRingCat.of B)).fromSpecResidueField s) ≫ x =
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B A)))
          ((Spec (CommRingCat.of B)).fromSpecResidueField s) ≫ y) ↔
      ∀ c : Γ(Spec (CommRingCat.of A), ⊤), j.appTop.hom c = 0 → ∀ i,
        bA.repr ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom c) i ∈ s.asIdeal := by
    intro s
    let _ : Algebra B ((Spec (CommRingCat.of B)).residueField s) :=
      (Spec.preimage ((Spec (CommRingCat.of B)).fromSpecResidueField s)).hom.toAlgebra
    have hres : (Spec (CommRingCat.of B)).fromSpecResidueField s =
        Spec.map (CommRingCat.ofHom
          (algebraMap B ((Spec (CommRingCat.of B)).residueField s))) :=
      (Spec.map_preimage _).symm
    rw [hres, ← cancel_epi (pullbackSpecIso B A ((Spec (CommRingCat.of B)).residueField s)).inv,
      pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_fst_assoc,
      comp_eq_iff_ker_le π x y h, ker_le_iff_of_isAffine]
    constructor
    · intro hle c hc i
      have h1 := hle (RingHom.mem_ker.2 hc)
      rw [RingHom.mem_ker, SpecMap_appTop_eq_zero_iff, CommRingCat.hom_ofHom,
        Algebra.TensorProduct.includeLeftRingHom_apply, tmul_one_eq_zero_iff bA] at h1
      exact (fromSpecResidueField_preimage_eq_zero_iff s _).1 (h1 i)
    · intro hc c hc'
      rw [RingHom.mem_ker] at hc'
      rw [RingHom.mem_ker, SpecMap_appTop_eq_zero_iff, CommRingCat.hom_ofHom,
        Algebra.TensorProduct.includeLeftRingHom_apply, tmul_one_eq_zero_iff bA]
      intro i
      exact (fromSpecResidueField_preimage_eq_zero_iff s _).2 (hc c hc' i)
  have hcl : ∀ r : B, IsClosed {s : Spec (CommRingCat.of B) | r ∈ s.asIdeal} := by
    intro r
    have : {s : Spec (CommRingCat.of B) | r ∈ s.asIdeal} =
        PrimeSpectrum.zeroLocus ({r} : Set B) := by
      ext s
      exact ((PrimeSpectrum.mem_zeroLocus s {r}).trans Set.singleton_subset_iff).symm
    rw [this]
    exact PrimeSpectrum.isClosed_zeroLocus _
  have hset : {s : Spec (CommRingCat.of B) |
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B A)))
          ((Spec (CommRingCat.of B)).fromSpecResidueField s) ≫ x =
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B A)))
          ((Spec (CommRingCat.of B)).fromSpecResidueField s) ≫ y} =
      ⋂ c : Γ(Spec (CommRingCat.of A), ⊤), ⋂ (_ : j.appTop.hom c = 0), ⋂ i,
        {s : Spec (CommRingCat.of B) |
          bA.repr ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom c) i ∈ s.asIdeal} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact key s
  rw [hset]
  exact isClosed_iInter fun c => isClosed_iInter fun _ => isClosed_iInter fun i => hcl _

/-- The underlying morphism of a base-changed homomorphism, followed by the first projection. -/
private theorem baseChange_map_left_fst {S T : Scheme.{u}} (q : T ⟶ S) {H G : GroupScheme S}
    (u : H ⟶ G) :
    ((GroupScheme.baseChange q).map u).hom.hom.left ≫ pullback.fst G.X.hom q =
      pullback.fst H.X.hom q ≫ u.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- The underlying morphism of a base-changed homomorphism, followed by the second
projection. -/
private theorem baseChange_map_left_snd {S T : Scheme.{u}} (q : T ⟶ S) {H G : GroupScheme S}
    (u : H ⟶ G) :
    ((GroupScheme.baseChange q).map u).hom.hom.left ≫ pullback.snd G.X.hom q =
      pullback.snd H.X.hom q :=
  pullback.lift_snd _ _ _

/-- Two homomorphisms agree after base change along `t` exactly when their underlying
morphisms agree after composition with the first projection of `H ×_S T`. -/
private theorem baseChange_map_eq_iff {S T : Scheme.{u}} (t : T ⟶ S) {H G : GroupScheme S}
    (a b : H ⟶ G) :
    (GroupScheme.baseChange t).map a = (GroupScheme.baseChange t).map b ↔
      pullback.fst H.X.hom t ≫ a.hom.hom.left = pullback.fst H.X.hom t ≫ b.hom.hom.left := by
  constructor
  · intro h
    rw [← baseChange_map_left_fst t a, ← baseChange_map_left_fst t b, h]
  · intro h
    apply Grp.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (baseChange_map_left_fst t a).trans (h.trans (baseChange_map_left_fst t b).symm)
    · exact (baseChange_map_left_snd t a).trans (baseChange_map_left_snd t b).symm

end MultiplicativeTypeTrivialLocusClosedProof

open MultiplicativeTypeTrivialLocusClosedProof RelativeMultiplicativeType

/-- SGA 3, Exposé IX, Corollaire 5.3, closedness part. -/
theorem multiplicativeTypeTrivialLocusClosed :
    MultiplicativeTypeTrivialLocusClosedStatement.{u} := by
  intro S H G hH hG u
  obtain ⟨𝒰, h𝒰⟩ := hH
  have hset : {s : S | ((GroupScheme.baseChange (S.fromSpecResidueField s)).map u).hom.hom = 1} =
      {s : S | pullback.fst H.X.hom (S.fromSpecResidueField s) ≫ u.hom.hom.left =
        pullback.fst H.X.hom (S.fromSpecResidueField s) ≫ (0 : H ⟶ G).hom.hom.left} := by
    ext s
    simp only [Set.mem_ofPred_eq]
    rw [CentralRigidity.hom_eq_one_iff_eq_zero,
      ← CentralRigidity.baseChange_map_zero (S.fromSpecResidueField s), baseChange_map_eq_iff]
  rw [hset]
  have hxy : u.hom.hom.left ≫ G.X.hom = (0 : H ⟶ G).hom.hom.left ≫ G.X.hom := by
    rw [Over.w, Over.w]
  refine isClosed_of_cover 𝒰.f (fun i => ?_) 𝒰.exists_eq H.X.hom _ _ (fun i => ?_)
  · have : Flat (𝒰.f i) := (𝒰.map_prop i).1
    have : LocallyOfFinitePresentation (𝒰.f i) := (𝒰.map_prop i).2
    exact (𝒰.f i).isOpenMap
  obtain ⟨Λ, _, _, ⟨e⟩⟩ := h𝒰 i
  let 𝒱 := (𝒰.X i).affineOpenCover
  refine isClosed_of_cover 𝒱.f (fun j => (𝒱.f j).isOpenEmbedding.isOpenMap)
    (fun v => ⟨𝒱.idx v, 𝒱.covers v⟩) _ _ _ (fun j => ?_)
  let B : CommRingCat.{u} := 𝒱.X j
  let a : Spec B ⟶ 𝒰.X i := 𝒱.f j
  let E : (GroupScheme.baseChange a).obj ((GroupScheme.baseChange (𝒰.f i)).obj H) ≅
      (Diagonalizable.groupScheme B Λ).toGrp :=
    (GroupScheme.baseChange a).mapIso e ≪≫ diagonalizableBaseChangeIso a Λ ≪≫
      (Diagonalizable.relativeModelIso B Λ).symm
  let k : Spec (CommRingCat.of (AddMonoidAlgebra B Λ)) ⟶
      pullback (pullback.snd H.X.hom (𝒰.f i)) a :=
    E.inv.hom.hom.left
  have : IsIso k := by
    have : IsIso E.inv.hom.hom := inferInstance
    exact Functor.map_isIso (Over.forget _) E.inv.hom.hom
  have hk : k ≫ pullback.snd (pullback.snd H.X.hom (𝒰.f i)) a =
      Spec.map (CommRingCat.ofHom (algebraMap B (AddMonoidAlgebra B Λ))) :=
    Over.w E.inv.hom.hom
  refine isClosed_locus_of_isIso k _ _ hk _ _ ?_
  refine isClosed_core (B := B) (AddMonoidAlgebra.basis Λ B) G.X.hom _ _ ?_
  simp only [Category.assoc, hxy]

end Langlands.GroupScheme
