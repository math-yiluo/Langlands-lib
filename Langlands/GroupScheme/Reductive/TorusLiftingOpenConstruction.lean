import Langlands.GroupScheme.Reductive.LiftedTorusNeighbourhood
import Langlands.GroupScheme.Torus.RelativeLiftingStatement
import Langlands.GroupScheme.Torus.FiniteGaloisSplitMaximal
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Open neighbourhoods from the actual split-torus lifting statement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

local instance liftingOpen_smooth_pullback {S U : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] (b : U ⟶ S) : Smooth ((baseChange b).obj G).X.hom :=
  inferInstanceAs (Smooth (Limits.pullback.snd G.X.hom b))

local instance liftingOpen_affine_pullback {S U : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] (b : U ⟶ S) : IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

/-- A split presentation of the supplied actual commutative relative torus
reduces its good-open construction to standard-torus coordinates. -/
def identityComponentReductiveNeighbourhood_of_splitTorus_fieldPoint
    (hCentralizer : AlgClosedMaximalTorusCentralizerStatement.{u})
    (hReflection : RelativeRootReflectionExistenceStatement.{u})
    (hReduced : RootReducednessStatement.{u})
    (hLine : SplitRootLieLineStatement.{u})
    {S : Scheme.{u}} (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (T : CommGroupScheme S) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsClosedSubgroup i)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (hs : b (IsLocalRing.closedPoint k) ∈ identityComponentReductiveLocus G)
    (hmax : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((baseChange b).map i)) :
    IdentityComponentReductiveOpenNeighbourhood G (b (IsLocalRing.closedPoint k)) :=
  Classical.choice <| by
    classical
    obtain ⟨I, hI, ⟨e⟩⟩ := hT
    let : Fintype I := Fintype.ofFinite I
    let j : splitTorus S I ⟶ G := e.inv ≫ i
    have hj : IsClosedSubgroup j := hi.iso_comp e.symm
    have hm : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj
        (splitTorus.commGroupScheme S I)) ((baseChange b).map j) := by
      have hm := IsMaximalTorus.iso_comp
        (T := (CommGroupScheme.baseChange b).obj T)
        (T' := (CommGroupScheme.baseChange b).obj (splitTorus.commGroupScheme S I))
        ((baseChange b).mapIso e.symm) hmax
      simpa only [j, Functor.map_comp, Functor.mapIso_hom, Iso.symm_hom] using hm
    exact ⟨splitTorus.identityComponentReductiveNeighbourhood_of_maximal_fieldPoint_overScheme
      hCentralizer hReflection hReduced hLine I G j hj b hs hm⟩

/-- The lifting statement's exact recovery equation preserves maximality of
the specified residue-field torus in the actual lifted field fibre. -/
theorem isMaximalTorus_of_lifting_recovery
    {S U : Scheme.{u}} (G : GroupScheme S) (s : S)
    (p : U ⟶ S) (b : Spec (S.residueField s) ⟶ U)
    (hb : b ≫ p = S.fromSpecResidueField s)
    (T : CommGroupScheme U) (T₀ : CommGroupScheme (Spec (S.residueField s)))
    (i : T.toGrp ⟶ (baseChange p).obj G)
    (i₀ : T₀.toGrp ⟶ (baseChange (S.fromSpecResidueField s)).obj G)
    (e : (baseChange b).obj T.toGrp ≅ T₀.toGrp)
    (he : (baseChange b).map i ≫ (baseChangeCompIso p b G).inv ≫
      (eqToIso (congrArg (fun f => (baseChange f).obj G) hb)).hom = e.hom ≫ i₀)
    (hmax : IsMaximalTorus (T := T₀) i₀) :
    IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((baseChange b).map i) := by
  let ε : ((baseChange b).obj ((baseChange p).obj G)) ≅
      (baseChange (S.fromSpecResidueField s)).obj G :=
    (baseChangeCompIso p b G).symm ≪≫
      eqToIso (congrArg (fun f => (baseChange f).obj G) hb)
  have he' : (baseChange b).map i ≫ ε.hom = e.hom ≫ i₀ := he
  apply (IsMaximalTorus.comp_iso_iff
    (T := (CommGroupScheme.baseChange b).obj T) ((baseChange b).map i) ε).mp
  rw [he']
  exact IsMaximalTorus.iso_comp
    (T := T₀) (T' := (CommGroupScheme.baseChange b).obj T) e hmax

/-- A specified split maximal torus in the actual residue fibre gives a good
original-base open through the retained actual lifting and field statements. -/
def identityComponentReductiveNeighbourhood_of_splitMaximalResidueTorus
    (hLift : RelativeSplitTorusLiftingStatement.{u})
    (hCentralizer : AlgClosedMaximalTorusCentralizerStatement.{u})
    (hReflection : RelativeRootReflectionExistenceStatement.{u})
    (hReduced : RootReducednessStatement.{u})
    (hLine : SplitRootLieLineStatement.{u})
    {S : Scheme.{u}} (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (s : S) (hs : s ∈ identityComponentReductiveLocus G)
    (T₀ : CommGroupScheme (Spec (S.residueField s))) (hT₀ : IsSplitTorus T₀.toGrp)
    (i₀ : T₀.toGrp ⟶ (baseChange (S.fromSpecResidueField s)).obj G)
    (hmax : IsMaximalTorus (T := T₀) i₀) :
    IdentityComponentReductiveOpenNeighbourhood G s :=
  Classical.choice <| by
    obtain ⟨U, p, hp, b, hb, T, hT, i, hi, e, he⟩ :=
      hLift S G s T₀.toGrp hT₀ i₀ hmax.2.1
    let : Etale p := hp
    let TC : CommGroupScheme U := { T with comm := hT.isCommMonObj }
    have hm : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj TC)
        ((baseChange b).map i) :=
      isMaximalTorus_of_lifting_recovery G s p b hb TC T₀ i i₀ e he hmax
    have hpoint : p (b (IsLocalRing.closedPoint (S.residueField s))) = s := by
      calc
        _ = S.fromSpecResidueField s (IsLocalRing.closedPoint (S.residueField s)) :=
          congrArg (fun f => f (IsLocalRing.closedPoint (S.residueField s))) hb
        _ = s := Scheme.fromSpecResidueField_apply _ _
    have hsU : b (IsLocalRing.closedPoint (S.residueField s)) ∈
        identityComponentReductiveLocus ((baseChange p).obj G) := by
      rw [identityComponentReductiveLocus_baseChange]
      change p (b (IsLocalRing.closedPoint (S.residueField s))) ∈
        identityComponentReductiveLocus G
      rwa [hpoint]
    let good := identityComponentReductiveNeighbourhood_of_splitTorus_fieldPoint
      hCentralizer hReflection hReduced hLine ((baseChange p).obj G) TC hT i hi b hsU hm
    have result := identityComponentReductiveOpenNeighbourhood_of_openMap G p p.isOpenMap
      (b (IsLocalRing.closedPoint (S.residueField s))) good.neighbourhood.isOpen
      good.mem_neighbourhood good.subset_locus
    exact ⟨by simpa only [hpoint] using result⟩

end Langlands.GroupScheme
