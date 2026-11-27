import Langlands.GroupScheme.Rational.QuadraticOppositeBorelExistence
import Langlands.GroupScheme.Dynamic.OppositeParabolicUniquenessProof
import Langlands.GroupScheme.Absolute.TripleCell

/-! # The three-factor open cell of a quadratic opposite-Borel torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

private theorem centralizer_transportCocharacter {B S : Scheme.{u}}
    (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b) (G : GroupScheme B)
    (χ : (Gm S).toGrp ⟶ (GroupScheme.baseChange b).obj G) :
    Dynamic.centralizer (transportCocharacter b a ha G χ) =
      SubgroupFunctor.descentTransport b a ha G (Dynamic.centralizer χ) := by
  let e := descentBaseChangeIso b a ha G
  have he : transportCocharacter b a ha G χ ≫ e.inv =
      Dynamic.baseChangeCocharacter a χ := by
    simp only [transportCocharacter, Dynamic.baseChangeCocharacter, e, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [Dynamic.centralizer_eq_comap_of_iso _ e.symm, Iso.symm_hom, he, Dynamic.centralizer_baseChange]
  rfl

private theorem unipotent_transportCocharacter {B S : Scheme.{u}}
    (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b) (G : GroupScheme B)
    (χ : (Gm S).toGrp ⟶ (GroupScheme.baseChange b).obj G) :
    Dynamic.unipotent (transportCocharacter b a ha G χ) =
      SubgroupFunctor.descentTransport b a ha G (Dynamic.unipotent χ) := by
  let e := descentBaseChangeIso b a ha G
  have he : transportCocharacter b a ha G χ ≫ e.inv =
      Dynamic.baseChangeCocharacter a χ := by
    simp only [transportCocharacter, Dynamic.baseChangeCocharacter, e, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [Dynamic.unipotent_eq_comap_of_iso _ e.symm, Iso.symm_hom, he, Dynamic.unipotent_baseChange]
  rfl

/-- The opposite-Borel torus has a cocharacter over the quadratic field
whose positive and negative unipotent factors are exchanged by conjugation. -/
theorem IsQuadraticOppositeBorelTorus.exists_torusDynamicData
    {F Q : Type u} [Field F] [Field Q] [Algebra F Q]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {t : T.toGrp ⟶ G}
    (hG : IsConnectedReductive G) (ht : IsQuadraticOppositeBorelTorus (Q := Q) t) :
    let b := algebraBaseMap F Q
    let tQ := (GroupScheme.baseChange b).map t
    ∃ (σ : Q ≃ₐ[F] Q) (ν : cocharacterLattice ((CommGroupScheme.baseChange b).obj T)),
      let χ := CommGroupScheme.groupHom ν ≫ tQ
      σ ≠ 1 ∧ Dynamic.centralizer χ = SubgroupFunctor.range tQ ∧
        SubgroupFunctor.galoisTransport F Q G σ (Dynamic.unipotent χ) =
          Dynamic.unipotent (Dynamic.oppositeCocharacter χ) := by
  dsimp only
  let b := algebraBaseMap F Q
  let C := GroupScheme.baseChange b
  let GQ := C.obj G
  let TQ := (CommGroupScheme.baseChange b).obj T
  let tQ := C.map t
  have hGQ : IsConnectedReductive GQ := connectedReductiveFieldExtensionStatement F Q G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom GQ.X.hom := hGQ.isAffineHom
  let : IsAffine GQ.X.left := isAffine_of_isAffineHom GQ.X.hom
  have htQ : IsMaximalTorus (T := TQ) tQ :=
    (maximalTorusBaseChange F Q G T t ht.2.1.1 ht.2.1.2.1).mp ht.2.1
  obtain ⟨_, _, σ, B, j, hσ, hj, hinter⟩ := ht
  let : IsClosedImmersion j.hom.hom.left := hj.1.isClosedSubgroup
  let hJ : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨Over.mono_of_mono_left _, rfl⟩
  have hle : SubgroupFunctor.range tQ ≤ SubgroupFunctor.range j := by
    rw [← hinter]
    exact fun _ _ hx => hx.1
  let f := hJ.liftOfLE tQ hle
  obtain ⟨ν, hP, hC, _⟩ := hj.exists_oppositeDynamicBorel hGQ htQ f (hJ.liftOfLE_comp tQ hle)
  let χ := CommGroupScheme.groupHom ν ≫ tQ
  let a := galoisBaseMap F Q σ
  let ha := galoisBaseMap_over F Q σ
  let χσ := transportCocharacter b a ha G χ
  have hPσ : Dynamic.parabolic χσ = SubgroupFunctor.range (radicalGaloisHom j σ) := by
    rw [Dynamic.parabolic_transportCocharacter_eq_descentTransport, ← hP.2,
      SubgroupFunctor.descentTransport_range]
    rfl
  have hCσ : Dynamic.centralizer χσ = Dynamic.centralizer χ := by
    rw [centralizer_transportCocharacter, hC, SubgroupFunctor.range_baseChangeHom,
      SubgroupFunctor.descentTransport_baseChange]
  have hI : Dynamic.parabolic χ ⊓ Dynamic.parabolic χσ = Dynamic.centralizer χ := by
    rw [← hP.2, hPσ, hC]
    exact hinter
  have hI' := congrArg (fun A : SubgroupFunctor GQ => A.carrier
    (Over.mk (𝟙 (Spec (CommRingCat.of Q))))) hI
  have hU := (oppositeDynamicParabolicUniqueness Q GQ hGQ χ χσ hCσ hI').2
  refine ⟨σ, ν, hσ, hC, ?_⟩
  exact (unipotent_transportCocharacter b a ha G χ).symm.trans hU

/-- The exchanged unipotent factors are those of a cocharacter of the
actual base-changed group with the given torus as centralizer. -/
theorem IsQuadraticOppositeBorelTorus.exists_dynamicData
    {F Q : Type u} [Field F] [Field Q] [Algebra F Q]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {t : T.toGrp ⟶ G}
    (hG : IsConnectedReductive G) (ht : IsQuadraticOppositeBorelTorus (Q := Q) t) :
    let b := algebraBaseMap F Q
    let GQ := (GroupScheme.baseChange b).obj G
    ∃ (σ : Q ≃ₐ[F] Q) (χ : (Gm (Spec (CommRingCat.of Q))).toGrp ⟶ GQ), σ ≠ 1 ∧
      Dynamic.centralizer χ = SubgroupFunctor.range ((GroupScheme.baseChange b).map t) ∧
      SubgroupFunctor.galoisTransport F Q G σ (Dynamic.unipotent χ) =
        Dynamic.unipotent (Dynamic.oppositeCocharacter χ) := by
  obtain ⟨σ, ν, hσ, hC, hU⟩ := ht.exists_torusDynamicData hG
  exact ⟨σ, CommGroupScheme.groupHom ν ≫ (GroupScheme.baseChange (algebraBaseMap F Q)).map t,
    hσ, hC, hU⟩

namespace Dynamic

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (t : T.toGrp ⟶ G)

/-- The product `U(χ) × T × U(-χ) → G` as an actual morphism of schemes. -/
abbrev torusOppositeCell :
    (Affine.unipotentScheme χ).X ⊗ (T.X ⊗ (Affine.unipotentScheme (oppositeCocharacter χ)).X) ⟶ G.X :=
  tripleCellMultiplication (Affine.unipotentHom χ) t (Affine.unipotentHom (oppositeCocharacter χ))

omit [IsAffineHom G.X.hom] in
/-- The opposite cell map multiplies its three supplied coordinates. -/
theorem lift_comp_torusOppositeCell {Z : Over (Spec (CommRingCat.of k))}
    (x : Z ⟶ (Affine.unipotentScheme χ).X) (y : Z ⟶ T.X)
    (z : Z ⟶ (Affine.unipotentScheme (oppositeCocharacter χ)).X) :
    lift x (lift y z) ≫ torusOppositeCell χ t =
      (x ≫ (Affine.unipotentHom χ).hom.hom) * (y ≫ t.hom.hom) *
        (z ≫ (Affine.unipotentHom (oppositeCocharacter χ)).hom.hom) := by
  rw [mul_assoc, lift_tripleCellMultiplication]

/-- The three-factor multiplication is an open immersion when the middle
torus represents the full dynamic centralizer. -/
theorem isOpenImmersion_torusOppositeCell [Smooth G.X.hom]
    (ht : (centralizer χ).IsRepresentedBy t) :
    IsOpenImmersion (torusOppositeCell χ t).left := by
  let χ' := oppositeCocharacter χ
  have hU : (unipotent (oppositeCocharacter χ')).IsRepresentedBy (Affine.unipotentHom χ) := by
    simpa only [χ', oppositeCocharacter_oppositeCocharacter] using Affine.isRepresentedBy_unipotentHom χ
  have ht' : (centralizer χ').IsRepresentedBy t := by
    rw [show centralizer χ' = centralizer χ from centralizer_oppositeCocharacter χ]
    exact ht
  exact isOpenImmersion_tripleCellMultiplication χ' hU ht' (Affine.isRepresentedBy_unipotentHom χ')

end Dynamic
end Langlands.GroupScheme
