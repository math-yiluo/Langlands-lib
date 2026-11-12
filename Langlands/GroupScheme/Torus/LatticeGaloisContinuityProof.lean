import Langlands.GroupScheme.Torus.LatticeGaloisContinuityStatement
import Langlands.GroupScheme.Descent.FiniteStageHom
import Langlands.GroupScheme.Torus.FiniteGaloisCharacterDescent
import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Torus.CharacterIsomorphism
import Langlands.GroupScheme.Absolute.CocharacterAveraging
import Langlands.GroupScheme.Torus.SplittingDescentHelpers
import Langlands.GroupScheme.CocharacterTransport

/-! # Continuity of the Galois action on the lattices of a torus: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace LatticeGaloisContinuity

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]

/-- An automorphism fixing an intermediate field pointwise fixes its spectrum map. -/
theorem galoisBaseMap_comp_of_fixes (E : FinIntermediateField k Ω) (σ : Ω ≃ₐ[k] Ω)
    (hσ : ∀ x ∈ E.1, σ x = x) :
    galoisBaseMap k Ω σ ≫ Spec.map (CommRingCat.ofHom (algebraMap E.1 Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap E.1 Ω)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext x
  exact hσ x.1 x.2

/-- The scheme-level form of a finite model: after projecting to the finite stage, the
original map is the model map. -/
theorem model_fst {G H : GroupScheme (Spec (CommRingCat.of k))}
    (E : FinIntermediateField k Ω)
    (g : (baseChange (algebraBaseMap k E.1)).obj G ⟶ (baseChange (algebraBaseMap k E.1)).obj H)
    (f : (baseChange (algebraBaseMap k Ω)).obj G ⟶ (baseChange (algebraBaseMap k Ω)).obj H)
    (hrec : (Descent.FiniteStage.comparison k Ω E G).hom ≫
        (baseChange (algebraBaseMap E.1 Ω)).map g =
      f ≫ (Descent.FiniteStage.comparison k Ω E H).hom) :
    f.hom.hom.left ≫ pullback.fst H.X.hom (algebraBaseMap k Ω) =
      (baseChangeCone (Ω := Ω) G.X.left G.X.hom).π.app (op E) ≫ g.hom.hom.left ≫
        pullback.fst H.X.hom (algebraBaseMap k E.1) := by
  have h := congrArg (fun φ => φ.hom.hom.left ≫ pullback.fst (pullback.snd H.X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap k E.1))))
      (Spec.map (CommRingCat.ofHom (algebraMap E.1 Ω)))) hrec
  simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc] at h
  rw [Descent.FiniteStage.comparison_hom_fst] at h
  have hg : ((baseChange (algebraBaseMap E.1 Ω)).map g).hom.hom.left ≫
      pullback.fst (pullback.snd H.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E.1))))
        (Spec.map (CommRingCat.ofHom (algebraMap E.1 Ω))) =
      pullback.fst (pullback.snd G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E.1))))
        (Spec.map (CommRingCat.ofHom (algebraMap E.1 Ω))) ≫ g.hom.hom.left := by
    simp
    exact pullback.lift_fst _ _ _
  have h2 := (congrArg (fun z => (Descent.FiniteStage.comparison k Ω E G).hom.hom.hom.left ≫ z)
    hg).symm.trans h
  simp only at h2
  rw [← Category.assoc, Descent.FiniteStage.comparison_hom_fst] at h2
  have hconeH : (baseChangeCone (Ω := Ω) H.X.left H.X.hom).π.app (op E) ≫
      pullback.fst H.X.hom (algebraBaseMap k E.1) = pullback.fst H.X.hom (algebraBaseMap k Ω) := by
    simp only [baseChangeCone_π_app]
    exact pullback.lift_fst _ _ _
  calc f.hom.hom.left ≫ pullback.fst H.X.hom (algebraBaseMap k Ω)
      = (f.hom.hom.left ≫ (baseChangeCone (Ω := Ω) H.X.left H.X.hom).π.app (op E)) ≫
          pullback.fst H.X.hom (algebraBaseMap k E.1) := by rw [Category.assoc, hconeH]
    _ = ((baseChangeCone (Ω := Ω) G.X.left G.X.hom).π.app (op E) ≫ g.hom.hom.left) ≫
          pullback.fst H.X.hom (algebraBaseMap k E.1) := by rw [← h2]
    _ = _ := Category.assoc _ _ _

/-- The finite-stage projection of a group over `k` is invariant under canonical descent
along an automorphism fixing the finite stage. -/
theorem cone_descent (G : GroupScheme (Spec (CommRingCat.of k)))
    (E : FinIntermediateField k Ω) (σ : Ω ≃ₐ[k] Ω) (hσ : ∀ x ∈ E.1, σ x = x) :
    pullback.fst (pullback.snd G.X.hom (algebraBaseMap k Ω)) (galoisBaseMap k Ω σ) ≫
        (baseChangeCone (Ω := Ω) G.X.left G.X.hom).π.app (op E) =
      (descentBaseChangeIso (algebraBaseMap k Ω) (galoisBaseMap k Ω σ)
          (galoisBaseMap_over k Ω σ) G).hom.hom.hom.left ≫
        (baseChangeCone (Ω := Ω) G.X.left G.X.hom).π.app (op E) := by
  have hac := galoisBaseMap_comp_of_fixes E σ hσ
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeCone_π_app, pullback.lift_fst, Category.comp_id]
    rw [descentBaseChangeIso_hom_fst]
  · simp only [Category.assoc, baseChangeCone_π_app, pullback.lift_snd]
    have hw : (descentBaseChangeIso (algebraBaseMap k Ω) (galoisBaseMap k Ω σ)
        (galoisBaseMap_over k Ω σ) G).hom.hom.hom.left ≫ pullback.snd G.X.hom (algebraBaseMap k Ω) =
        pullback.snd (pullback.snd G.X.hom (algebraBaseMap k Ω)) (galoisBaseMap k Ω σ) :=
      (descentBaseChangeIso (algebraBaseMap k Ω) (galoisBaseMap k Ω σ)
        (galoisBaseMap_over k Ω σ) G).hom.hom.hom.w
    rw [reassoc_of% hw, pullback.condition_assoc]
    exact congrArg (fun z => pullback.snd (pullback.snd G.X.hom (algebraBaseMap k Ω))
      (galoisBaseMap k Ω σ) ≫ z) hac

/-- A homomorphism of base changes with a finite model commutes with canonical descent along
every automorphism fixing the field of definition. -/
theorem descent_comm_of_model {G H : GroupScheme (Spec (CommRingCat.of k))}
    (E : FinIntermediateField k Ω)
    (g : (baseChange (algebraBaseMap k E.1)).obj G ⟶ (baseChange (algebraBaseMap k E.1)).obj H)
    (f : (baseChange (algebraBaseMap k Ω)).obj G ⟶ (baseChange (algebraBaseMap k Ω)).obj H)
    (hrec : (Descent.FiniteStage.comparison k Ω E G).hom ≫
        (baseChange (algebraBaseMap E.1 Ω)).map g =
      f ≫ (Descent.FiniteStage.comparison k Ω E H).hom)
    (σ : Ω ≃ₐ[k] Ω) (hσ : ∀ x ∈ E.1, σ x = x) :
    (baseChange (galoisBaseMap k Ω σ)).map f ≫
        (descentBaseChangeIso (algebraBaseMap k Ω) (galoisBaseMap k Ω σ)
          (galoisBaseMap_over k Ω σ) H).hom =
      (descentBaseChangeIso (algebraBaseMap k Ω) (galoisBaseMap k Ω σ)
          (galoisBaseMap_over k Ω σ) G).hom ≫ f := by
  have hfst := model_fst E g f hrec
  have hcone := cone_descent G E σ hσ
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc]
    rw [descentBaseChangeIso_hom_fst, hfst]
    have hmap : ((baseChange (galoisBaseMap k Ω σ)).map f).hom.hom.left ≫
        pullback.fst (pullback.snd H.X.hom (algebraBaseMap k Ω)) (galoisBaseMap k Ω σ) =
        pullback.fst (pullback.snd G.X.hom (algebraBaseMap k Ω)) (galoisBaseMap k Ω σ) ≫
          f.hom.hom.left := by
      simp
      exact pullback.lift_fst _ _ _
    rw [reassoc_of% hmap, hfst, reassoc_of% hcone]
  · have h1 := ((baseChange (galoisBaseMap k Ω σ)).map f ≫
      (descentBaseChangeIso (algebraBaseMap k Ω) (galoisBaseMap k Ω σ)
        (galoisBaseMap_over k Ω σ) H).hom).hom.hom.w
    have h2 := ((descentBaseChangeIso (algebraBaseMap k Ω) (galoisBaseMap k Ω σ)
        (galoisBaseMap_over k Ω σ) G).hom ≫ f).hom.hom.w
    exact h1.trans h2.symm

/-- If `T_Ω` is identified with the base change of a split torus over `k` by an isomorphism
with a finite model, every automorphism fixing the field of definition fixes all characters
of `T_Ω`. -/
theorem characters_fixed {T S₀ : CommGroupScheme (Spec (CommRingCat.of k))}
    (hS₀ : IsSplitTorus S₀.toGrp)
    (e : (CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj T ≅
      (CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj S₀)
    (E : FinIntermediateField k Ω)
    (g : (baseChange (algebraBaseMap k E.1)).obj T.toGrp ⟶
      (baseChange (algebraBaseMap k E.1)).obj S₀.toGrp)
    (hrec : (Descent.FiniteStage.comparison k Ω E T.toGrp).hom ≫
        (baseChange (algebraBaseMap E.1 Ω)).map g =
      CommGroupScheme.groupHom e.hom ≫ (Descent.FiniteStage.comparison k Ω E S₀.toGrp).hom)
    (σ : Ω ≃ₐ[k] Ω) (hσ : ∀ x ∈ E.1, σ x = x)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj T)) :
    characterLattice.galoisRepresentation k Ω T σ χ = χ := by
  have hdesc := descent_comm_of_model E g (CommGroupScheme.groupHom e.hom) hrec σ hσ
  have htrans : galoisHomTransport σ e.hom = e.hom := by
    change Additive.ofMul ((descentBaseChangeIso (algebraBaseMap k Ω) (galoisBaseMap k Ω σ)
        (galoisBaseMap_over k Ω σ) T.toGrp).inv ≫
      (baseChange (galoisBaseMap k Ω σ)).map (CommGroupScheme.groupHom e.hom) ≫
      (descentBaseChangeIso (algebraBaseMap k Ω) (galoisBaseMap k Ω σ)
        (galoisBaseMap_over k Ω σ) S₀.toGrp).hom) = e.hom
    rw [hdesc, Iso.inv_hom_id_assoc]
    rfl
  obtain ⟨ψ₀, hψ₀⟩ := (hS₀.characterLattice_baseChange_bijective (algebraBaseMap k Ω) S₀).2
    (e.inv ≫ χ)
  have hχ : χ = e.hom ≫ characterLattice.baseChange (algebraBaseMap k Ω) S₀ ψ₀ := by
    rw [hψ₀, Iso.hom_inv_id_assoc]
  rw [hχ, ← galoisHomTransport_comp, htrans, characterLattice.galoisRepresentation_baseChange]

/-- For a split torus, an automorphism whose inverse fixes every character fixes every
cocharacter, by the Galois invariance of the lattice pairing. -/
theorem cocharacters_fixed {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj T).toGrp)
    (σ : Ω ≃ₐ[k] Ω)
    (hχ : ∀ χ, characterLattice.galoisRepresentation k Ω T σ⁻¹ χ = χ)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj T)) :
    cocharacterLattice.galoisRepresentation k Ω T σ ν = ν := by
  apply hT.hom_ext_of_characters
  intro χ
  apply (gmEndEquiv Ω).injective
  have h := latticePairing_galoisRepresentation_right k Ω T σ χ ν
  rw [hχ] at h
  exact h

end LatticeGaloisContinuity

open LatticeGaloisContinuity in
/-- The Galois action on the lattices of a torus split over an algebraic extension factors
through the fixer of a finite subextension. -/
theorem torusLatticeGaloisContinuity : TorusLatticeGaloisContinuityStatement.{u} := by
  intro k E _ _ _ _ T hsplit
  have hTt : IsTorus T.toGrp := ⟨E, inferInstance, inferInstance, hsplit⟩
  have := hTt.quasiCompact
  have := hTt.quasiSeparated
  obtain ⟨I, hI, ⟨e⟩⟩ := hsplit
  let S₀ := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I
  have hS₀ : IsSplitTorus S₀.toGrp := isSplitTorus_splitTorus I
  have := hS₀.isTorus.smooth
  let e' : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T ≅
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj S₀ :=
    CommGroupScheme.isoOfGroupIso (e ≪≫ (splitTorus.baseChangeIso (algebraBaseMap k E) I).symm)
  let D := Descent.FiniteStage.homModel k E (CommGroupScheme.groupHom e'.hom)
  refine ⟨D.fieldOfDefinition.1, D.fieldOfDefinition.2, fun σ hσ => ?_⟩
  have hfix : ∀ τ : E ≃ₐ[k] E, (∀ x ∈ D.fieldOfDefinition.1, τ x = x) →
      ∀ χ, characterLattice.galoisRepresentation k E T τ χ = χ :=
    fun τ hτ χ => characters_fixed hS₀ e' D.fieldOfDefinition D.hom D.recovery τ hτ χ
  have hσinv : ∀ x ∈ D.fieldOfDefinition.1, σ⁻¹ x = x := fun x hx =>
    σ.symm_apply_eq.2 (hσ x hx).symm
  refine ⟨LinearMap.ext fun χ => hfix σ hσ χ, LinearMap.ext fun ν => ?_⟩
  exact cocharacters_fixed ⟨I, hI, ⟨e⟩⟩ σ (hfix σ⁻¹ hσinv) ν

end Langlands.GroupScheme
