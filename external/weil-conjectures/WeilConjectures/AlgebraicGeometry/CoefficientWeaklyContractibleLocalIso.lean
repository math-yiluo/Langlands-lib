/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
import WeilConjectures.AlgebraicGeometry.ProEtale.WContractibleDisjointCover
import WeilConjectures.CategoryTheory.RingedDerivedDisjointIso
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-! # Local derived isomorphisms on a weakly contractible affine object

Source: Stacks Project, Tags 090K and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem sectionOfCoefficientCover
    (X : Scheme.{u}) (U V : coefficientProEtaleSiteModel.{u, v} X) (p : V ⟶ U)
    (hp : Sieve.generate (Presieve.singleton p) ∈ coefficientProEtaleModelTopology X U)
    (hweak : AdicResidueSliceWeaklyContractible X U) :
    ∃ s : U ⟶ V, s ≫ p = 𝟙 U := by
  let J := coefficientProEtaleModelTopology.{u, v} X
  have : (AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).IsEquivalence :=
    (AsSmall.equiv (C := X.ProEt)).isEquivalence_inverse
  have : J.Subcanonical := GrothendieckTopology.subcanonical_of_full_of_faithful
    (AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt) J (ProEt.topology X)
  let q : Over.mk p ⟶ Over.mk (𝟙 U) := Over.homMk p
  have hq : Sieve.generate (Presieve.singleton q) ∈ J.over U (Over.mk (𝟙 U)) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
    rw [← Sieve.arrows_generate_map_eq_functorPushforward,
      Presieve.map_singleton, Sieve.generate_sieve]
    change Sieve.generate (Presieve.singleton p) ∈ J U
    exact hp
  let K := J.over U
  have hepi : Epi (K.uliftYoneda.map q) := by
    constructor
    intro Z a b hab
    apply K.uliftYonedaEquiv.injective
    have heq : Z.obj.map q.op (K.uliftYonedaEquiv a) =
        Z.obj.map q.op (K.uliftYonedaEquiv b) := by
      rw [K.uliftYonedaEquiv_naturality, K.uliftYonedaEquiv_naturality, hab]
    apply Sheaf.isSeparated Z _ _ hq
    rintro T f ⟨_, g, _, ⟨⟩, rfl⟩
    simpa only [op_comp, Functor.map_comp, types_comp_apply] using
      congrArg (Z.obj.map g.op) heq
  obtain ⟨s, hs⟩ := hweak _ _ (K.uliftYoneda.map q) hepi ⟨𝟙 _⟩
  exact ⟨(ULift.down s).left, congrArg (fun t ↦ t.down.left) hs⟩

private theorem coefficientFiniteDisjointRefinement
    (X : Scheme.{u}) (U : coefficientProEtaleSiteModel.{u, v} X)
    (hU : IsAffine (ULift.down U).left) (hweak : AdicResidueSliceWeaklyContractible X U)
    (S : Sieve U) (hS : S ∈ coefficientProEtaleModelTopology X U) :
    ∃ (n : ℕ) (Y : Fin n → coefficientProEtaleSiteModel.{u, v} X)
      (f : ∀ i, Y i ⟶ U),
      (coefficientProEtaleModelTopology X).IsDisjointCover f ∧ ∀ i, S (f i) := by
  classical
  let J := coefficientProEtaleModelTopology.{u, v} X
  let d : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt := AsSmall.down
  let a : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X := AsSmall.up
  have : d.IsEquivalence := (AsSmall.equiv (C := X.ProEt)).isEquivalence_inverse
  have : a.IsEquivalence := (AsSmall.equiv (C := X.ProEt)).isEquivalence_functor
  let S' := S.functorPushforward d
  have hS' : S' ∈ ProEt.topology X (ULift.down U) :=
    (CoverPreserving.of_isContinuous d J (ProEt.topology X)).cover_preserve hS
  obtain ⟨P, hP, hPS⟩ := ProEt.mem_topology_iff.mp hS'
  obtain ⟨𝒰, _, h𝒰⟩ := (mem_propQCPrecoverage_iff_exists_quasiCompactCover
    (P := @WeaklyEtale)).mp (ProEt.mem_precoverage_iff.mp hP)
  have : IsAffine (ULift.down U).left := hU
  obtain ⟨𝒱, g, hfin, _⟩ := Cover.QuasiCompact.exists_hom.{u + 1, u} 𝒰
  have : Finite 𝒱.I₀ := hfin
  have hmem (i : 𝒰.I₀) : P.map (ProEt.forget X ⋙ Over.forget X) (𝒰.f i) := by
    rw [h𝒰]
    exact ⟨i⟩
  choose Z hZ b hb hZb using fun i ↦ Presieve.map_iff.mp (hmem i)
  let ε : ULift.{u} (Fin (Nat.card 𝒱.I₀)) ≃ 𝒱.I₀ :=
    Equiv.ulift.trans (Finite.equivFin _).symm
  let v (k : ULift.{u} (Fin (Nat.card 𝒱.I₀))) := 𝒱.f (ε k)
  have : WeaklyEtale (Sigma.desc v) :=
    IsZariskiLocalAtSource.sigmaDesc fun k ↦ 𝒱.map_prop _
  have : Surjective (Sigma.desc v) := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨k, hk⟩ := ε.surjective (𝒱.idx x)
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    dsimp only [v]
    rw [hk]
    exact 𝒱.covers x
  let T : X.ProEt := ProEt.mk (Sigma.desc v ≫ (ULift.down U).hom)
  let p : T ⟶ (ULift.down U) := MorphismProperty.Over.homMk (Sigma.desc v) rfl
  have hp : Sieve.generate (Presieve.singleton p) ∈ ProEt.topology X (ULift.down U) := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [ProEt.mem_precoverage_iff, Presieve.map_singleton]
    change Presieve.singleton (Sigma.desc v) ∈ proetalePrecoverage _
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance
  have hp' : Sieve.generate (Presieve.singleton (a.map p)) ∈ J U := by
    have h := (CoverPreserving.of_isContinuous a (ProEt.topology X) J).cover_preserve hp
    rw [← Sieve.generate_map_eq_functorPushforward, Presieve.map_singleton] at h
    exact h
  obtain ⟨s, hs⟩ := sectionOfCoefficientCover X U (a.obj T) (a.map p) hp' hweak
  have hs' : (ULift.down s).left ≫ Sigma.desc v = 𝟙 (ULift.down U).left :=
    congrArg (fun f ↦ f.down.left) hs
  obtain ⟨Yd, fd, hf, hfS⟩ := ProEt.isDisjointCover_of_comp_sigmaDesc_eq_id
    v (ULift.down s).left hs' S' (by
      intro j Y c e he
      have hb' (i : 𝒰.I₀) : (b i).left = eqToHom (hZ i) ≫ 𝒰.f i := hZb i
      let t : Y.left ⟶ (Z (g.s₀ (ε j))).left :=
        e ≫ g.h₀ (ε j) ≫ eqToHom (hZ _).symm
      have ht : t ≫ (b (g.s₀ (ε j))).left = c.left := by
        rw [← he, hb', Category.assoc, Category.assoc, eqToHom_trans_assoc,
          eqToHom_refl, Category.id_comp, g.w₀]
        rfl
      have hc : c = MorphismProperty.Over.homMk t (by
          rw [← MorphismProperty.Over.w (b (g.s₀ (ε j))), ← Category.assoc, ht]
          exact MorphismProperty.Over.w c) ≫ b (g.s₀ (ε j)) :=
        MorphismProperty.Over.Hom.ext ht.symm
      rw [hc]
      exact S'.downward_closed (hPS _ _ (hb _)) _)
  let Y (i : Fin (Nat.card 𝒱.I₀)) := a.obj (Yd ⟨i⟩)
  let f (i : Fin (Nat.card 𝒱.I₀)) : Y i ⟶ U := a.map (fd ⟨i⟩)
  have hcov : Sieve.ofArrows Y f ∈ J U := by
    have h := (CoverPreserving.of_isContinuous a (ProEt.topology X) J).cover_preserve
      hf.ofArrows_mem
    rw [Sieve.functorPushforward_ofArrows] at h
    apply J.superset_covering _ h
    rintro W t ⟨Z, c, q, ⟨k⟩, rfl⟩
    rcases k with ⟨k⟩
    exact ⟨_, c, _, ⟨k⟩, rfl⟩
  refine ⟨_, Y, f, ⟨hcov, ?_, ?_⟩, ?_⟩
  · intro i
    have := hf.mono ⟨i⟩
    exact inferInstanceAs (Mono (a.map (fd ⟨i⟩)))
  · intro i j hij W c e he
    have h := hf.bot_mem ⟨i⟩ ⟨j⟩ (fun h ↦ hij (congrArg ULift.down h))
      (d.map c) (d.map e) (congrArg (fun k ↦ d.map k) he)
    have h' := (CoverPreserving.of_isContinuous a (ProEt.topology X) J).cover_preserve h
    rw [Sieve.functorPushforward_bot] at h'
    have heW : a.obj (d.obj W) = W := ULift.ext rfl
    exact heW ▸ h'
  · intro i
    have h := hfS ⟨i⟩
    change (S'.functorPullback d) (f i) at h
    simpa only [S', Sieve.functorPullback_functorPushforward_eq] using h

/-- Local isomorphisms of two complexes globalize on a weakly contractible affine.
Source: Stacks Project, Sites, Tag 090K; Pro-etale Cohomology, proof of Tag 09C6.
(auxiliary; not a blueprint node).

Proof: undo AsSmall and refine the covering sieve by finitely many affine
pro-etale objects. Their finite coproduct covers U. On the coefficient-sized
slice, its representable maps epimorphically to the representable of U. Apply
the stated terminal-section surjectivity to the identity section; subcanonicity
and Yoneda give a section of the coproduct cover. Pull back the coproduct
components along this section to obtain a finite disjoint cover of U contained
in the original sieve, and transport it through AsSmall. Apply the general
ringed derived disjoint-cover gluing theorem to the supplied component
isomorphisms. That theorem glues chain maps and inverse homotopies between
K-injective representatives, so it works for arbitrary unbounded complexes and
also for the empty cover. No coefficient finiteness or etale localization
comparison is required. -/
theorem coefficient_weaklyContractible_local_iso
    (X : Scheme.{u}) (B : Type (max v (u + 1))) [CommRing B]
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (hU : IsAffine ((AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).obj
      U).left)
    (hweak : AdicResidueSliceWeaklyContractible.{u, v} X U)
    (L N : ConstantCompletion.D
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B))
    (hlocal : ∃ S : Sieve U, S ∈ coefficientProEtaleModelTopology.{u, v} X U ∧
      ∀ (V : coefficientProEtaleSiteModel.{u, v} X) (f : V ⟶ U), S f →
        Nonempty ((adicResidueRestriction
          (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B) V).obj
            L ≅ (adicResidueRestriction
          (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B) V).obj
            N)) :
    Nonempty ((adicResidueRestriction
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B) U).obj L ≅
      (adicResidueRestriction
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B) U).obj
        N) := by
  obtain ⟨S, hS, hlocal⟩ := hlocal
  obtain ⟨n, Y, f, hf, hSf⟩ := coefficientFiniteDisjointRefinement X U hU hweak S hS
  exact CategoryTheory.ringedDerived_disjoint_iso
    (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B)
    U L N n Y f hf (fun i ↦ hlocal (Y i) (f i) (hSf i))

end AlgebraicGeometry.Scheme
