import Langlands.GroupScheme.Torus.HenselianSubgroupLifting
import Langlands.GroupScheme.Torus.HenselianSplitSubgroupLifting
import Langlands.GroupScheme.Torus.HenselianSplitTorusConjugacy
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent

/-! # Lifting residue tori containing a prescribed integral split torus -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- Split-source maps with the same residue map are conjugate by an integral
section reducing to the identity. -/
theorem exists_henselian_hom_conjugacy_of_residue_eq
    {R k : Type u} [CommRing R] [HenselianLocalRing R] [Field k] [Algebra R k]
    (hk : Function.Surjective (algebraMap R k))
    {H G : GroupScheme (Spec (CommRingCat.of R))}
    [IsAffineHom G.X.hom] (hG : Smooth G.X.hom) (hH : IsSplitTorus H)
    (j₁ j₂ : H ⟶ G)
    (he : (baseChange (Spec.algebraMap R k)).map j₂ =
      (baseChange (Spec.algebraMap R k)).map j₁) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X,
      j₂ ≫ (G.innerIso g).hom = j₁ ∧
        baseChangeSectionHom (Spec.algebraMap R k) G g = 1 := by
  let b := Spec.algebraMap R k
  have ht : PointwiseSchemeAction.IsTransporter
      ((baseChange b).map j₁) ((baseChange b).map j₂)
      (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ ((baseChange b).obj G).X) := by
    apply PointwiseSchemeAction.isTransporter_of_comp_innerIso_eq
    rw [innerIso_one_hom, Category.comp_id]
    exact he
  let c : Over.mk b ⟶ (Over.map b).obj (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
    Over.homMk (𝟙 _) (by simp)
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨g, hg, hrec⟩ := PointwiseSchemeAction.exists_henselian_transporter_of_split
    j₁ j₂ hH hG hk (c ≫ baseChangePointsEquiv b G _ 1)
    ((ht.baseChangePointsEquiv b).restrict c)
  refine ⟨g, hg.comp_innerIso_eq, ?_⟩
  apply (baseChangePointsEquiv b G _).injective
  rw [baseChangePointsEquiv_baseChangeSectionHom]
  apply Over.OverMorphism.ext
  have hh := congrArg Over.Hom.left hrec
  change b ≫ g.left = (𝟙 (Spec (CommRingCat.of k))) ≫
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ ((baseChange b).obj G).X).left ≫
      Limits.pullback.fst G.X.hom b at hh
  change b ≫ g.left =
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ ((baseChange b).obj G).X).left ≫
      Limits.pullback.fst G.X.hom b
  simpa only [Category.id_comp] using hh

namespace HenselianTorusLifting

variable {R k : Type u} [CommRing R] [HenselianLocalRing R] [Field k] [Algebra R k]

/-- An exact residue-torus lift that contains the prescribed integral split
source through an actual closed homomorphism. -/
structure ContainingLiftData
    {H G : GroupScheme (Spec (CommRingCat.of R))} (s : H ⟶ G)
    {T₀ : GroupScheme (Spec (CommRingCat.of k))}
    (i₀ : T₀ ⟶ (baseChange (Spec.algebraMap R k)).obj G)
    extends LiftData G i₀ where
  subtorusHom : H ⟶ torus
  subtorusClosed : IsClosedSubgroup subtorusHom
  contains : subtorusHom ≫ inclusion = s

/-- Lift a residue torus together with containment of a supplied integral
split torus, retaining the original residue torus inclusion exactly. -/
theorem nonempty_containingLiftData
    (hk : Function.Surjective (algebraMap R k))
    {H G : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (s : H ⟶ G) (hH : IsSplitTorus H)
    {T₀ : GroupScheme (Spec (CommRingCat.of k))}
    (i₀ : T₀ ⟶ (baseChange (Spec.algebraMap R k)).obj G)
    (hi₀ : IsClosedSubgroup i₀) (hT₀ : RelativeTorus.IsTorus T₀)
    (j₀ : (baseChange (Spec.algebraMap R k)).obj H ⟶ T₀)
    (hj₀ : IsClosedSubgroup j₀)
    (hji : j₀ ≫ i₀ = (baseChange (Spec.algebraMap R k)).map s) :
    Nonempty (ContainingLiftData s i₀) := by
  let b := Spec.algebraMap R k
  let L := liftData hk G i₀ hi₀ hT₀
  let : Smooth L.torus.X.hom := L.relativeTorus.smooth_of_isLocalRing
  let : IsAffineHom L.torus.X.hom := L.closed.isAffineHom
  let l := henselianClosedSplitHomLift hk H L.torus hH
    (j₀ ≫ L.residueIso.inv) (hj₀.comp_iso L.residueIso.symm)
  have hl : (baseChange b).map (l.val ≫ L.inclusion) =
      (baseChange b).map s := by
    rw [Functor.map_comp, l.property.2, L.residue_comm,
      Category.assoc, Iso.inv_hom_id_assoc]
    exact hji
  obtain ⟨g, hg, hgres⟩ := exists_henselian_hom_conjugacy_of_residue_eq
    hk inferInstance hH s (l.val ≫ L.inclusion) hl
  let i := L.inclusion ≫ (G.innerIso g).hom
  have hires : (baseChange b).map i = L.residueIso.hom ≫ i₀ := by
    rw [Functor.map_comp, baseChange_innerIso_hom]
    change (baseChange b).map L.inclusion ≫
      (((baseChange b).obj G).innerIso (baseChangeSectionHom b G g)).hom = _
    rw [hgres, innerIso_one_hom, Category.comp_id]
    exact L.residue_comm
  exact ⟨{
    torus := L.torus
    inclusion := i
    closed := L.closed.comp_iso (G.innerIso g)
    relativeTorus := L.relativeTorus
    residueIso := L.residueIso
    residue_comm := hires
    subtorusHom := l.val
    subtorusClosed := l.property.1
    contains := by simpa only [i, Category.assoc] using hg }⟩

/-- Choose an exact residue lift containing the prescribed split integral
torus through a closed source homomorphism. -/
def containingLiftData
    (hk : Function.Surjective (algebraMap R k))
    {H G : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (s : H ⟶ G) (hH : IsSplitTorus H)
    {T₀ : GroupScheme (Spec (CommRingCat.of k))}
    (i₀ : T₀ ⟶ (baseChange (Spec.algebraMap R k)).obj G)
    (hi₀ : IsClosedSubgroup i₀) (hT₀ : RelativeTorus.IsTorus T₀)
    (j₀ : (baseChange (Spec.algebraMap R k)).obj H ⟶ T₀)
    (hj₀ : IsClosedSubgroup j₀)
    (hji : j₀ ≫ i₀ = (baseChange (Spec.algebraMap R k)).map s) :
    ContainingLiftData s i₀ :=
  Classical.choice (nonempty_containingLiftData hk s hH i₀ hi₀ hT₀ j₀ hj₀ hji)

end HenselianTorusLifting
end Langlands.GroupScheme
