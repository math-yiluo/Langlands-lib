import Langlands.Geometry.Building.KPApartment
import Langlands.Geometry.Building.FiniteRealTorusSpace
import Langlands.GroupScheme.Rational.CrossTorusLieTransport
import Langlands.GroupScheme.Rational.CrossTorusWeylTransport

/-! # Translation spaces under actual transport between torus embeddings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}

/-- Simultaneous transport of actual characters and cocharacters preserves evaluation. -/
theorem eval_cocharacterRealCongr (e : S ≅ S') (a : characterLattice S) (v : V S) :
    eval S' (characterLattice.congr e a) (cocharacterRealCongr e v) = eval S a v := by
  simpa only [eval_eq_pair, characterRealCongr_tmul, characterLattice.congr_apply] using
    pair_congr e (1 ⊗ₜ[ℤ] a) v

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (e : S ≅ S') (f : G ≅ H)
  (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)

include f h

/-- The actual torus isomorphism preserves and reflects the common root kernel. -/
theorem cocharacterRealCongr_mem_rootAnnihilator_iff (v : V S) :
    cocharacterRealCongr e v ∈ rootAnnihilator j ↔ v ∈ rootAnnihilator i := by
  rw [mem_rootAnnihilator, mem_rootAnnihilator]
  constructor
  · intro hv a ha
    have hm := hv (characterLattice.congr e a) ((roots_mem_of_transport_iff e f h a).mpr ha)
    rwa [eval_cocharacterRealCongr] at hm
  · intro hv b hb
    obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective b
    rw [eval_cocharacterRealCongr]
    exact hv a ((roots_mem_of_transport_iff e f h a).mp hb)

/-- The transported common root kernel is exactly the target common root kernel. -/
theorem map_cocharacterRealCongr_rootAnnihilator :
    (rootAnnihilator i).map (cocharacterRealCongr e : V S →ₗ[ℝ] V S') =
      rootAnnihilator j := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (cocharacterRealCongr_mem_rootAnnihilator_iff e f h w).mpr hw
  · intro hv
    obtain ⟨w, rfl⟩ := (cocharacterRealCongr e).surjective v
    exact ⟨w, (cocharacterRealCongr_mem_rootAnnihilator_iff e f h w).mp hv, rfl⟩

/-- The actual torus isomorphism induces the map on reduced apartment translations. -/
def translationSpaceTransportEquiv : TranslationSpace i ≃ₗ[ℝ] TranslationSpace j :=
  Submodule.Quotient.equiv _ _ (cocharacterRealCongr e)
    (map_cocharacterRealCongr_rootAnnihilator e f h)

/-- On quotient representatives the map is precisely actual cocharacter transport. -/
@[simp] theorem translationSpaceTransportEquiv_mk (v : V S) :
    translationSpaceTransportEquiv e f h (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (cocharacterRealCongr e v) := rfl

/-- Actual root forms agree under the same character and quotient transport. -/
theorem rootForm_translationSpaceTransportEquiv (a : relativeRoots i)
    (v : TranslationSpace i) :
    rootForm j (relativeRootsTransportEquiv e f h a)
        (translationSpaceTransportEquiv e f h v) = rootForm i a v := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  exact eval_cocharacterRealCongr e a.val w

section Action

variable [Mono i.hom.hom.left] [Mono j.hom.hom.left]

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
/-- The same ambient isomorphism intertwines the actual normalizer cocharacter actions. -/
theorem cocharacterRealCongr_normalizerAction (n : normalizerPoints i) (v : V S) :
    cocharacterRealCongr e (normalizerAction i n v) =
      normalizerAction j (normalizerPointsTransportEquiv e f h n)
        (cocharacterRealCongr e v) := by
  have hσ : normalizingAut j (normalizerPointsTransportEquiv e f h n) =
      e.symm ≪≫ normalizingAut i n ≪≫ e :=
    (isNormalizingPoint_normalizingAut j _).unique j
      ((isNormalizingPoint_normalizingAut i n).transport e f h)
  induction v using TensorProduct.inductionOn with
  | tmul r ν =>
    simp only [normalizerAction_tmul, cocharacterRealCongr_tmul, hσ,
      Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- Quotient transport intertwines the original actual normalizer derivatives. -/
theorem translationSpaceTransportEquiv_translationAction (n : normalizerPoints i)
    (v : TranslationSpace i) :
    translationSpaceTransportEquiv e f h (translationAction i n v) =
      translationAction j (normalizerPointsTransportEquiv e f h n)
        (translationSpaceTransportEquiv e f h v) := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  rw [translationAction_mk, translationSpaceTransportEquiv_mk,
    translationSpaceTransportEquiv_mk, translationAction_mk]
  exact congrArg Submodule.Quotient.mk (cocharacterRealCongr_normalizerAction e f h n w)

end Action

end Langlands.Geometry.Building
