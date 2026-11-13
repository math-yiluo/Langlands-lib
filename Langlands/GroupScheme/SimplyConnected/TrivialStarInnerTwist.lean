import Langlands.GroupScheme.Adjoint.ExistenceProof
import Langlands.GroupScheme.Rational.PinnedGaloisInnerTwist
import Langlands.GroupScheme.Reductive.PinningBaseChange
import Langlands.GroupScheme.Reductive.StarAction
import Langlands.GroupScheme.Torus.LatticeBaseInvariants
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Pinned base-change isomorphisms onto groups with trivial star action are inner twists -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace TrivialStarInnerTwist

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- The Galois action on the characters of the base change of a split torus is trivial. -/
theorem galoisRepresentation_of_isSplitTorus
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (σ : L ≃ₐ[k] L)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)) :
    characterLattice.galoisRepresentation k L T σ χ = χ := by
  obtain ⟨χ₀, rfl⟩ :=
    (characterLattice.baseChangeEquiv (algebraBaseMap k L) T hT).surjective χ
  exact characterLattice.galoisRepresentation_baseChange k L T σ χ₀

local instance trivialStarBaseChangeAffine (k E : Type u) [Field k] [Field E] [Algebra k E]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

variable {M G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom M.X.hom]
  [IsAffineHom G.X.hom] [Algebra.IsAlgebraic k L]
  (pM : SplitPinning M) (d : GaloisPinningData k L G)
  (E : SplitPinning.Iso (pM.baseChange (F := L)) d.toSplitPinning)

/-- The torus isomorphism `E_T` of the pinned isomorphism, with its domain written as the
base change of the `k`-torus of `pM`. -/
def torusIso : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj pM.torus ≅
    (CommGroupScheme.baseChange (algebraBaseMap k L)).obj d.torus :=
  E.torusIso

/-- The automorphism `σ^*E ∘ E⁻¹` of `G_L`. -/
def twistIso (σ : L ≃ₐ[k] L) :
    (GroupScheme.baseChange (algebraBaseMap k L)).obj G ≅
      (GroupScheme.baseChange (algebraBaseMap k L)).obj G :=
  E.groupIso.symm ≪≫
    Descent.pullIso (galoisBaseMap k L σ) (galoisBaseMap_over k L σ)
      (galoisBaseMap_over k L σ) E.groupIso

/-- The torus automorphism of `T'_L` induced by `σ^*E ∘ E⁻¹`. -/
def twistTorusIso (σ : L ≃ₐ[k] L) :
    (CommGroupScheme.baseChange (algebraBaseMap k L)).obj d.torus ≅
      (CommGroupScheme.baseChange (algebraBaseMap k L)).obj d.torus :=
  (torusIso pM d E).symm ≪≫
    (CommGroupScheme.descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
      (galoisBaseMap_over k L σ) pM.torus).symm ≪≫
    (CommGroupScheme.baseChange (galoisBaseMap k L σ)).mapIso (torusIso pM d E) ≪≫
    CommGroupScheme.descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
      (galoisBaseMap_over k L σ) d.torus

/-- The twist automorphism normalizes the pinned torus through `twistTorusIso`. -/
theorem inclusion_comp_twistIso (σ : L ≃ₐ[k] L) :
    d.toSplitPinning.inclusion ≫ (twistIso pM d E σ).hom =
      CommGroupScheme.groupHom (twistTorusIso pM d E σ).hom ≫ d.toSplitPinning.inclusion := by
  have ha := galoisBaseMap_over k L σ
  have sq := E.square
  have sq' : d.toSplitPinning.inclusion ≫ E.groupIso.inv =
      CommGroupScheme.groupHom E.torusIso.inv ≫ (pM.baseChange (F := L)).inclusion := by
    rw [Iso.comp_inv_eq, Category.assoc, sq, ← Category.assoc]
    change _ = CommGroupScheme.groupHom (E.torusIso.inv ≫ E.torusIso.hom) ≫ _
    rw [Iso.inv_hom_id]
    exact (Category.id_comp _).symm
  have nM := descentBaseChangeIso_naturality (algebraBaseMap k L) (galoisBaseMap k L σ) ha
    pM.inclusion
  have nd := descentBaseChangeIso_naturality (algebraBaseMap k L) (galoisBaseMap k L σ) ha
    d.inclusion
  have nM' : (pM.baseChange (F := L)).inclusion ≫
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ) ha M).inv =
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ) ha
          pM.torus.toGrp).inv ≫
        (GroupScheme.baseChange (galoisBaseMap k L σ)).map
          ((GroupScheme.baseChange (algebraBaseMap k L)).map pM.inclusion) := by
    rw [Iso.comp_inv_eq, Category.assoc, nM, Iso.inv_hom_id_assoc]
    rfl
  have e1 : (twistIso pM d E σ).hom = E.groupIso.inv ≫
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ) ha M).inv ≫
      (GroupScheme.baseChange (galoisBaseMap k L σ)).map E.groupIso.hom ≫
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ) ha G).hom := rfl
  have e2 : CommGroupScheme.groupHom (twistTorusIso pM d E σ).hom =
      CommGroupScheme.groupHom E.torusIso.inv ≫
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ) ha
        pM.torus.toGrp).inv ≫
      (GroupScheme.baseChange (galoisBaseMap k L σ)).map
        (CommGroupScheme.groupHom E.torusIso.hom) ≫
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ) ha
        d.torus.toGrp).hom := rfl
  rw [e1, e2]
  rw [reassoc_of% sq', reassoc_of% nM', ← Functor.map_comp_assoc]
  change _ ≫ _ ≫ (GroupScheme.baseChange (galoisBaseMap k L σ)).map
    ((pM.baseChange (F := L)).inclusion ≫ E.groupIso.hom) ≫ _ = _
  rw [sq, Functor.map_comp_assoc]
  change _ ≫ _ ≫ _ ≫ (GroupScheme.baseChange (galoisBaseMap k L σ)).map
    ((GroupScheme.baseChange (algebraBaseMap k L)).map d.inclusion) ≫ _ = _
  rw [nd]
  simp only [Category.assoc]
  rfl

/-- On characters, the torus twist is the ordinary Galois action. -/
theorem characterAut_twistTorusIso_apply (σ : L ≃ₐ[k] L)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj d.torus)) :
    characterAut (twistTorusIso pM d E σ) χ =
      characterLattice.galoisRepresentation k L d.torus σ χ := by
  have key : ∀ ξ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj
      pM.torus),
      (CommGroupScheme.descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) pM.torus).hom ≫ ξ =
        (CommGroupScheme.baseChange (galoisBaseMap k L σ)).map ξ ≫
          (Gm.commBaseChangeIso (galoisBaseMap k L σ)).hom := by
    intro ξ
    have h := galoisRepresentation_of_isSplitTorus pM.torus pM.isSplitTorus σ ξ
    change (CommGroupScheme.descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) pM.torus).inv ≫
      (CommGroupScheme.baseChange (galoisBaseMap k L σ)).map ξ ≫
        (Gm.commBaseChangeIso (galoisBaseMap k L σ)).hom = ξ at h
    exact ((Iso.inv_comp_eq _).mp h).symm
  change (twistTorusIso pM d E σ).inv ≫ χ =
    (CommGroupScheme.descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) d.torus).inv ≫
      (CommGroupScheme.baseChange (galoisBaseMap k L σ)).map χ ≫
        (Gm.commBaseChangeIso (galoisBaseMap k L σ)).hom
  simp only [twistTorusIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]
  rw [key, Functor.map_comp]
  simp only [Category.assoc, Iso.map_inv_hom_id_assoc]

section Weyl

variable [LocallyOfFiniteType G.X.hom]

/-- If the star action of `σ` is trivial, the torus twist acts on characters through the
actual Weyl image of the pinned torus of `G_L`. -/
theorem characterAut_twistTorusIso_mem_weylImage (σ : L ≃ₐ[k] L) (hσ : d.starAction σ = 1)
    [Mono d.toSplitPinning.inclusion.hom.hom.left] :
    characterAut (twistTorusIso pM d E σ) ∈ weylImage d.toSplitPinning.inclusion := by
  refine d.toSplitPinning.isRootDatum.abstractWeylImage_le
    ⟨d.galoisAction σ, (d.starAction_eq_one_iff σ).mp hσ, ?_⟩
  apply LinearEquiv.ext
  intro χ
  exact (characterAut_twistTorusIso_apply pM d E σ χ).symm

variable [FiniteDimensional k L] [IsGalois k L]

/-- A pinned isomorphism from the base change of a split group onto `G_L`, where the star
action of every element of `Gal(L/k)` on the pinning data of `G` is trivial, has all-test
inner discrepancy with respect to any actual adjoint quotient of the split group. -/
theorem hasInnerDiscrepancy (hstar : ∀ σ : L ≃ₐ[k] L, d.starAction σ = 1)
    {A : GroupScheme (Spec (CommRingCat.of k))} {q : M ⟶ A} (hq : IsAdjointQuotient q) :
    (LocalGroupIso.ofBaseChangeIso
      (U := Langlands.AlgebraicGeometry.PointTopology.ringTest k L)
        E.groupIso).HasInnerDiscrepancy hq.innerAction := by
  obtain ⟨A', q', hq'⟩ := adjointQuotientExistence L _ d.isConnectedReductive
  let : IsClosedImmersion d.toSplitPinning.inclusion.hom.hom.left := d.isMaximalTorus.2.1
  apply IsAdjointQuotient.hasInnerDiscrepancy_of_galois_baseChange hq E.groupIso
  intro σ
  let hqK := adjointQuotientBaseChangeStatement.isAdjointQuotient (K := L) hq
  let Φ := hqK.mapIso hq' E.groupIso
  obtain ⟨y, hy⟩ := d.toSplitPinning.exists_adjointPoint_of_weylImage hq'
    (twistIso pM d E σ) (twistTorusIso pM d E σ) (inclusion_comp_twistIso pM d E σ)
    (characterAut_twistTorusIso_mem_weylImage pM d E σ (hstar σ))
  refine ⟨y ≫ Φ.inv.hom.hom, ?_⟩
  have hxy : (y ≫ Φ.inv.hom.hom) ≫ Φ.hom.hom.hom = y := by
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id]
    exact Category.comp_id y
  rw [hqK.basePointIso_trans hq' E.groupIso, hxy, hy, twistIso]
  ext
  simp

end Weyl

end TrivialStarInnerTwist

end Langlands.GroupScheme
