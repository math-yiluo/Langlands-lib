import Langlands.GroupScheme.Torus.ExponentCocharacters
import Langlands.GroupScheme.Torus.GeometricRootProfiles
import Langlands.GroupScheme.Dynamic.RelativeCentralizerComparison
import Langlands.GroupScheme.Reductive.RootTangentRankOneReduction

/-! # Actual relative fixed-exponent cocharacter centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Dynamic

section FieldWeight

variable {k : Type u} [Field k]
  {G C : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom C.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ζ : cocharacterLattice T) {j : C ⟶ G}
  (hj : (centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)
  (α : characterLattice T) (hα : latticePairing T α ζ = 0)

include hα

/-- The actual differential weight comparison as a linear equivalence.
No reductivity or smoothness premise is used. -/
def centralizerWeightSpaceEquiv :
    weightSpace (torusFactor i (CommGroupScheme.groupHom ζ) hj) α ≃ₗ[k]
      weightSpace i α := by
  let : Mono j.hom.hom := hj.1
  exact (Submodule.equivMapOfInjective (Lie.targetMapLinear j k)
    (Lie.targetMapLinear_injective j k)
    (weightSpace (torusFactor i (CommGroupScheme.groupHom ζ) hj) α)).trans
      (LinearEquiv.ofEq _ _ (RootReducedness.map_weightSpace_torusFactor i ζ hj hα))

@[simp] theorem centralizerWeightSpaceEquiv_coe
    (X : weightSpace (torusFactor i (CommGroupScheme.groupHom ζ) hj) α) :
    (centralizerWeightSpaceEquiv i ζ hj α hα X : Additive (lieKernel G k)) =
      Lie.targetMapLinear j k X := rfl

omit hα in
/-- The roots in an actual represented cocharacter centralizer are precisely
the ambient roots annihilating that cocharacter. -/
theorem mem_roots_torusFactor_iff :
    α ∈ roots (torusFactor i (CommGroupScheme.groupHom ζ) hj) ↔
      α ∈ roots i ∧ latticePairing T α ζ = 0 :=
  ⟨RootReducedness.mem_roots_of_mem_roots_torusFactor i ζ hj,
    fun h => RootReducedness.mem_roots_torusFactor i ζ hj h.1 h.2⟩

end FieldWeight

end Dynamic

namespace splitTorus.RelativeCocharacterCentralizer

variable {r : Type u} [CommRing r] (I : Type u) [Fintype I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G) (n : I → ℤ)

local instance affine_ambient : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The actual ambient cocharacter determined by a fixed integer vector. -/
def cocharacter : (Gm (Spec (CommRingCat.of r))).toGrp ⟶ G :=
  CommGroupScheme.groupHom (exponentCocharacter _ I n) ≫ i

/-- The actual affine relative centralizer, defined without reductivity. -/
abbrev groupScheme : GroupScheme (Spec (CommRingCat.of r)) :=
  Dynamic.Affine.centralizerScheme (cocharacter I G i n)

/-- Its specified closed subgroup inclusion into the supplied ambient group. -/
def inclusion : groupScheme I G i n ⟶ G :=
  Dynamic.Affine.centralizerHom (cocharacter I G i n)

theorem isClosedSubgroup_inclusion : IsClosedSubgroup (inclusion I G i n) :=
  Dynamic.Affine.isClosedSubgroup_centralizerHom _

theorem isRepresentedBy_inclusion :
    (Dynamic.centralizer (cocharacter I G i n)).IsRepresentedBy (inclusion I G i n) :=
  Dynamic.Affine.isRepresentedBy_centralizerHom _

instance affine_groupScheme : IsAffineHom (groupScheme I G i n).X.hom :=
  (isClosedSubgroup_inclusion I G i n).isAffineHom

instance smooth_groupScheme [Smooth G.X.hom] : Smooth (groupScheme I G i n).X.hom :=
  Dynamic.smooth_affineCentralizer_overRing _ inferInstance

/-- The supplied actual standard torus factors through the relative centralizer. -/
def torusHom : splitTorus (Spec (CommRingCat.of r)) I ⟶ groupScheme I G i n :=
  Dynamic.torusFactor (T := commGroupScheme _ I) i
    (CommGroupScheme.groupHom (exponentCocharacter _ I n))
    (isRepresentedBy_inclusion I G i n)

@[reassoc (attr := simp)] theorem torusHom_comp :
    torusHom I G i n ≫ inclusion I G i n = i :=
  Dynamic.torusFactor_comp _ _ _

theorem isClosedSubgroup_torusHom (hi : IsClosedSubgroup i) :
    IsClosedSubgroup (torusHom I G i n) :=
  IsClosedSubgroup.of_comp (isClosedSubgroup_inclusion I G i n) (by
    rwa [torusHom_comp])

section BaseChange

variable {R' : CommRingCat.{u}} (b : Spec R' ⟶ Spec (CommRingCat.of r))

/-- The actual torus map in an arbitrary affine base change of the ambient family. -/
def baseChangedTorusHom : splitTorus (Spec R') I ⟶ (baseChange b).obj G :=
  (baseChangeIso b I).inv ≫ (baseChange b).map i

omit [IsAffineHom G.X.hom] in
/-- The actual fixed-exponent cocharacter has the same integer coordinates
after every affine base change. -/
theorem cocharacter_baseChange :
    Dynamic.baseChangeCocharacter b (cocharacter I G i n) =
      CommGroupScheme.groupHom (exponentCocharacter (Spec R') I n) ≫
        baseChangedTorusHom I G i b := by
  have he := groupHom_exponentCocharacter_baseChange (Spec (CommRingCat.of r)) I b n
  have he' : Dynamic.baseChangeCocharacter b
      (CommGroupScheme.groupHom (exponentCocharacter (Spec (CommRingCat.of r)) I n)) =
        CommGroupScheme.groupHom (exponentCocharacter (Spec R') I n) ≫
          (baseChangeIso b I).inv := by
    rw [← he]
    simp
  change Dynamic.baseChangeCocharacter b
    (CommGroupScheme.groupHom (exponentCocharacter (Spec (CommRingCat.of r)) I n) ≫ i) = _
  simpa only [Dynamic.baseChangeCocharacter, Functor.map_comp, Category.assoc,
    baseChangedTorusHom] using congrArg (fun f => f ≫ (baseChange b).map i) he'

/-- The actual pullback of the relative inclusion represents the centralizer
of the same fixed-coordinate cocharacter on every test over the new base. -/
theorem isRepresentedBy_baseChangeInclusion :
    (Dynamic.centralizer
      (CommGroupScheme.groupHom (exponentCocharacter (Spec R') I n) ≫
        baseChangedTorusHom I G i b)).IsRepresentedBy
      ((baseChange b).map (inclusion I G i n)) := by
  rw [← cocharacter_baseChange]
  exact Dynamic.isRepresentedBy_centralizer_baseChange b _
    (isRepresentedBy_inclusion I G i n)

end BaseChange

section Geometric

variable [Smooth G.X.hom] (s : Spec (CommRingCat.of r))

local instance smooth_geometric_ambient :
    Smooth (geometricFiber G s).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

local instance affine_geometric_ambient :
    IsAffineHom (geometricFiber G s).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

local instance smooth_geometric_centralizer :
    Smooth (geometricFiber (groupScheme I G i n) s).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd
    (groupScheme I G i n).X.hom (geometricPoint _ s)))

local instance affine_geometric_centralizer :
    IsAffineHom (geometricFiber (groupScheme I G i n) s).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd
    (groupScheme I G i n).X.hom (geometricPoint _ s)))

/-- The same fixed-coordinate actual cocharacter inside the actual geometric
identity component of the original ambient family. -/
def geometricIdentityCocharacter :
    (Gm (Spec (CommRingCat.of
      (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))))).toGrp ⟶
        identityComponent (geometricFiber G s) :=
  CommGroupScheme.groupHom (exponentCocharacter _ I n) ≫
    geometricIdentityComponentHom I G i s

/-- The actual induced inclusion of geometric identity components. -/
def geometricIdentityInclusion :
    identityComponent (geometricFiber (groupScheme I G i n) s) ⟶
      identityComponent (geometricFiber G s) :=
  IdentityComponent.map ((baseChange (geometricPoint _ s)).map (inclusion I G i n))

/-- The identity component of the actual relative centralizer fibre represents
the actual cocharacter centralizer inside the original geometric identity component. -/
theorem isRepresentedBy_geometricIdentityInclusion :
    (Dynamic.centralizer (geometricIdentityCocharacter I G i n s)).IsRepresentedBy
      (geometricIdentityInclusion I G i n s) := by
  apply Dynamic.identityComponent_map_represents_centralizer
    (geometricIdentityCocharacter I G i n s)
    ((baseChange (geometricPoint _ s)).map (inclusion I G i n))
  · simpa only [geometricIdentityCocharacter, Category.assoc,
      geometricIdentityComponentHom_comp, baseChangedTorusHom, geometricFiberHom] using
      isRepresentedBy_baseChangeInclusion I G i n (geometricPoint _ s)
  · exact (isClosedSubgroup_inclusion I G i n).baseChange _

@[reassoc (attr := simp)] theorem geometricIdentityTorusHom_comp :
    geometricIdentityComponentHom I (groupScheme I G i n) (torusHom I G i n) s ≫
        geometricIdentityInclusion I G i n s =
      geometricIdentityComponentHom I G i s := by
  apply (cancel_mono (identityComponentι (geometricFiber G s))).mp
  simp only [Category.assoc, geometricIdentityInclusion,
    IdentityComponent.map_identityComponentι,
    geometricIdentityComponentHom_comp_assoc, geometricIdentityComponentHom_comp]
  change (baseChangeIso (geometricPoint _ s) I).inv ≫
      (baseChange (geometricPoint _ s)).map (torusHom I G i n) ≫
      (baseChange (geometricPoint _ s)).map (inclusion I G i n) = _
  rw [← Functor.map_comp, torusHom_comp]
  rfl

/-- The canonical torus map in the relative centralizer's geometric identity
component is the actual factor of the original torus through the represented
centralizer in the original identity component. -/
theorem geometricIdentityTorusHom_eq_factor :
    geometricIdentityComponentHom I (groupScheme I G i n) (torusHom I G i n) s =
      Dynamic.torusFactor (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s)
        (CommGroupScheme.groupHom (exponentCocharacter _ I n))
        (isRepresentedBy_geometricIdentityInclusion I G i n s) :=
  (isRepresentedBy_geometricIdentityInclusion I G i n s).hom_ext
    ((geometricIdentityTorusHom_comp I G i n s).trans
      (Dynamic.torusFactor_comp _ _ _).symm)

/-- The roots of the actual centralizer identity component are exactly the
ambient roots annihilating the fixed integer cocharacter vector. -/
theorem mem_geometricCentralizerExponentRoots_iff (m : I → ℤ) :
    m ∈ geometricExponentRoots I (groupScheme I G i n) (torusHom I G i n) s ↔
      m ∈ geometricExponentRoots I G i s ∧ ∑ j, m j * n j = 0 := by
  change exponentCharacter _ I m ∈ roots
    (T := commGroupScheme _ I)
    (geometricIdentityComponentHom I (groupScheme I G i n) (torusHom I G i n) s) ↔
      exponentCharacter _ I m ∈ roots (T := commGroupScheme _ I)
        (geometricIdentityComponentHom I G i s) ∧ _
  rw [geometricIdentityTorusHom_eq_factor]
  simpa only [latticePairing_exponentCharacter_exponentCocharacter] using
    Dynamic.mem_roots_torusFactor_iff
      (k := AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))
      (T := commGroupScheme _ I)
      (geometricIdentityComponentHom I G i s) (exponentCocharacter _ I n)
      (isRepresentedBy_geometricIdentityInclusion I G i n s) (exponentCharacter _ I m)

/-- Every actual weight surviving in the centralizer has exactly its original
ambient dimension, through the actual centralizer inclusion differential. -/
theorem finrank_geometricCentralizerWeight (m : I → ℤ)
    (hm : ∑ j, m j * n j = 0) :
    Module.finrank (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))
        (weightSpace (T := commGroupScheme _ I)
          (geometricIdentityComponentHom I (groupScheme I G i n) (torusHom I G i n) s)
          (exponentCharacter _ I m)) =
      Module.finrank (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))
        (weightSpace (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s)
          (exponentCharacter _ I m)) := by
  rw [geometricIdentityTorusHom_eq_factor]
  apply LinearEquiv.finrank_eq (Dynamic.centralizerWeightSpaceEquiv
    (k := AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))
    (T := commGroupScheme _ I)
    (geometricIdentityComponentHom I G i s) (exponentCocharacter _ I n)
    (isRepresentedBy_geometricIdentityInclusion I G i n s) (exponentCharacter _ I m) ?_)
  rwa [latticePairing_exponentCharacter_exponentCocharacter]

end Geometric

end splitTorus.RelativeCocharacterCentralizer

end Langlands.GroupScheme
