import Langlands.AbelianScheme.MultiplicationSpecialization
import Langlands.AbelianScheme.TorsionBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

universe u
variable {S T : Scheme.{u}}

/-- The kernel of an abelian-scheme homomorphism, as an actual group scheme. -/
abbrev kernel {A B : AbelianScheme S} (f : A ⟶ B) : Grp (Over S) :=
  GroupScheme.kernel (groupHom f)

/-- The canonical group-scheme inclusion of the kernel. -/
abbrev kernelι {A B : AbelianScheme S} (f : A ⟶ B) : kernel f ⟶ A.toGrp :=
  GroupScheme.kernelι (groupHom f)

/-- The kernel is the actual scheme pullback along the target unit section. -/
lemma kernel_isPullback_scheme {A B : AbelianScheme S} (f : A ⟶ B) :
    IsPullback (kernelι f).hom.hom.left (kernel f).X.hom
      (hom f) η[B.X].left :=
  GroupScheme.kernel_isPullback_scheme (groupHom f)

/-- Properness of the target makes every such kernel inclusion closed. -/
instance kernelι_isClosedImmersion {A B : AbelianScheme S} (f : A ⟶ B) :
    IsClosedImmersion (kernelι f).hom.hom.left :=
  GroupScheme.kernelι_isClosedImmersion (groupHom f)

/-- On every test scheme the scheme kernel is the actual homomorphism kernel. -/
abbrev kernelPointsEquiv {A B : AbelianScheme S} (f : A ⟶ B) (U : Over S) :=
  GroupScheme.kernelPointsEquiv (groupHom f) U

lemma kernelPointsEquiv_naturality {A B : AbelianScheme S} (f : A ⟶ B)
    {U V : Over S} (a : V ⟶ U) (x : U ⟶ (kernel f).X) :
    kernelPointsEquiv f V (a ≫ x) =
      GroupScheme.kernelPointsRestrict (groupHom f) a (kernelPointsEquiv f U x) :=
  GroupScheme.kernelPointsEquiv_naturality (groupHom f) a x

/-- The kernel comparison for arbitrary base change of abelian schemes. -/
abbrev kernelBaseChangeIso (b : T ⟶ S) {A B : AbelianScheme S} (f : A ⟶ B) :
    (GroupScheme.baseChange b).obj (kernel f) ≅ kernel ((baseChange b).map f) :=
  GroupScheme.kernelBaseChangeIso b (groupHom f)

@[reassoc (attr := simp)]
lemma kernelBaseChangeIso_hom_ι (b : T ⟶ S) {A B : AbelianScheme S} (f : A ⟶ B) :
    (kernelBaseChangeIso b f).hom ≫ kernelι ((baseChange b).map f) =
      (GroupScheme.baseChange b).map (kernelι f) :=
  GroupScheme.kernelBaseChangeIso_hom_ι b (groupHom f)

lemma kernelBaseChangeIso_points (b : T ⟶ S) {A B : AbelianScheme S}
    (f : A ⟶ B) (U : Over T)
    (x : U ⟶ ((GroupScheme.baseChange b).obj (kernel f)).X) :
    GroupScheme.baseChangeKernelPointsEquiv b (groupHom f) U
      (kernelPointsEquiv ((baseChange b).map f) U
        (x ≫ (kernelBaseChangeIso b f).hom.hom.hom)) =
      kernelPointsEquiv f ((Over.map b).obj U)
        (GroupScheme.baseChangePointsEquiv b (kernel f) U x) :=
  GroupScheme.kernelBaseChangeIso_points b (groupHom f) U x

/-- Integer torsion is the already-constructed kernel group scheme. -/
abbrev torsion (A : AbelianScheme S) (n : ℤ) : Grp (Over S) :=
  GroupScheme.torsion A.toGrp n

/-- The inclusion of integer torsion into the underlying group scheme. -/
abbrev torsionι (A : AbelianScheme S) (n : ℤ) : torsion A n ⟶ A.toGrp :=
  GroupScheme.torsionι A.toGrp n

lemma torsion_eq_kernel (A : AbelianScheme S) (n : ℤ) :
    torsion A n = kernel (multiplication A n) := rfl

instance torsionι_isClosedImmersion (A : AbelianScheme S) (n : ℤ) :
    IsClosedImmersion (torsionι A n).hom.hom.left :=
  GroupScheme.torsionι_isClosedImmersion A.toGrp n

/-- The scheme fibre-product square defining torsion. -/
lemma torsion_isPullback_scheme (A : AbelianScheme S) (n : ℤ) :
    IsPullback (torsionι A n).hom.hom.left (torsion A n).X.hom
      (hom (multiplication A n)) η[A.X].left :=
  GroupScheme.torsion_isPullback_scheme A.toGrp n

/-- The actual subgroup of points killed by integer multiplication. -/
abbrev torsionPoints (A : AbelianScheme S) (n : ℤ) (U : Over S) :=
  GroupScheme.torsionPoints A.toGrp n U

/-- The canonical multiplicative equivalence on all test schemes. -/
abbrev torsionPointsEquiv (A : AbelianScheme S) (n : ℤ) (U : Over S) :
    (U ⟶ (torsion A n).X) ≃* torsionPoints A n U :=
  GroupScheme.torsionPointsEquiv A.toGrp n U

@[simp]
lemma mem_torsionPoints (A : AbelianScheme S) (n : ℤ)
    (U : Over S) (x : U ⟶ A.X) : x ∈ torsionPoints A n U ↔ x ^ n = 1 :=
  GroupScheme.mem_torsionPoints A.toGrp n U x

lemma torsionPointsEquiv_naturality (A : AbelianScheme S) (n : ℤ)
    {U V : Over S} (a : V ⟶ U) (x : U ⟶ (torsion A n).X) :
    torsionPointsEquiv A n V (a ≫ x) =
      GroupScheme.torsionPointsRestrict A.toGrp n a (torsionPointsEquiv A n U x) :=
  GroupScheme.torsionPointsEquiv_naturality A.toGrp n a x

lemma existsUnique_torsion_lift_iff (A : AbelianScheme S) (n : ℤ)
    (U : Over S) (x : U ⟶ A.X) :
    (∃! y : U ⟶ (torsion A n).X, y ≫ (torsionι A n).hom.hom = x) ↔ x ^ n = 1 :=
  GroupScheme.existsUnique_torsion_lift_iff A.toGrp n U x

/-- Torsion of abelian schemes commutes with arbitrary base change. -/
abbrev torsionBaseChangeIso (b : T ⟶ S) (A : AbelianScheme S) (n : ℤ) :
    (GroupScheme.baseChange b).obj (torsion A n) ≅
      torsion ((baseChange b).obj A) n :=
  GroupScheme.torsionBaseChangeIso b A.toGrp n

@[reassoc (attr := simp)]
lemma torsionBaseChangeIso_hom_ι (b : T ⟶ S) (A : AbelianScheme S) (n : ℤ) :
    (torsionBaseChangeIso b A n).hom ≫ torsionι ((baseChange b).obj A) n =
      (GroupScheme.baseChange b).map (torsionι A n) :=
  GroupScheme.torsionBaseChangeIso_hom_ι b A.toGrp n

@[reassoc (attr := simp)]
lemma torsionBaseChangeIso_inv_ι (b : T ⟶ S) (A : AbelianScheme S) (n : ℤ) :
    (torsionBaseChangeIso b A n).inv ≫ (GroupScheme.baseChange b).map (torsionι A n) =
      torsionι ((baseChange b).obj A) n :=
  GroupScheme.torsionBaseChangeIso_inv_ι b A.toGrp n

/-- The actual torsion subgroups agree under the pullback point equivalence. -/
abbrev baseChangeTorsionPointsEquiv (b : T ⟶ S) (A : AbelianScheme S) (n : ℤ)
    (U : Over T) :
    torsionPoints ((baseChange b).obj A) n U ≃*
      torsionPoints A n ((Over.map b).obj U) :=
  GroupScheme.baseChangeTorsionPointsEquiv b A.toGrp n U

lemma torsionBaseChangeIso_points (b : T ⟶ S) (A : AbelianScheme S) (n : ℤ)
    (U : Over T) (x : U ⟶ ((GroupScheme.baseChange b).obj (torsion A n)).X) :
    baseChangeTorsionPointsEquiv b A n U
      (torsionPointsEquiv ((baseChange b).obj A) n U
        (x ≫ (torsionBaseChangeIso b A n).hom.hom.hom)) =
      torsionPointsEquiv A n ((Over.map b).obj U)
        (GroupScheme.baseChangePointsEquiv b (torsion A n) U x) :=
  GroupScheme.torsionBaseChangeIso_points b A.toGrp n U x

end Langlands.AbelianScheme
