import Langlands.GroupScheme.RepresentedSubgroupTransport
import Langlands.GroupScheme.Rational.CrossTorusKernelCentralizer

/-! # Represented root subgroups and kernel centralizers under transport -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {B : Scheme.{u}} {S S' : CommGroupScheme B} {G H K K' : GroupScheme B}
variable {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
variable {k : K ⟶ G} {k' : K' ⟶ H}

/-- The supplied representatives of the actual root subgroup functors are
isomorphic by restriction of the supplied ambient isomorphism. -/
def subgroupTransportIso (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (hk : (subgroup i a).IsRepresentedBy k)
    (hk' : (subgroup j (characterLattice.congr e a)).IsRepresentedBy k') : K ≅ K' :=
  hk.isoOfComap hk' f (subgroup_comap_of_transport e f h a)

@[reassoc] theorem subgroupTransportIso_hom_comp (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (hk : (subgroup i a).IsRepresentedBy k)
    (hk' : (subgroup j (characterLattice.congr e a)).IsRepresentedBy k') :
    (subgroupTransportIso e f h a hk hk').hom ≫ k' = k ≫ f.hom :=
  hk.isoOfComap_hom_comp hk' f (subgroup_comap_of_transport e f h a)

@[reassoc] theorem subgroupTransportIso_inv_comp (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (hk : (subgroup i a).IsRepresentedBy k)
    (hk' : (subgroup j (characterLattice.congr e a)).IsRepresentedBy k') :
    (subgroupTransportIso e f h a hk hk').inv ≫ k = k' ≫ f.inv :=
  hk.isoOfComap_inv_comp hk' f (subgroup_comap_of_transport e f h a)

/-- The scheme isomorphism induces the previously constructed actual point
equivalence on every scheme test. -/
theorem subgroupTransportIso_pointsEquiv (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (hk : (subgroup i a).IsRepresentedBy k)
    (hk' : (subgroup j (characterLattice.congr e a)).IsRepresentedBy k')
    {U : Over B} (x : U ⟶ K.X) :
    hk'.pointsEquiv U (x ≫ (subgroupTransportIso e f h a hk hk').hom.hom.hom) =
      subgroupTransportEquiv e f h a U (hk.pointsEquiv U x) := by
  apply Subtype.ext
  exact hk.isoOfComap_hom_points hk' f (subgroup_comap_of_transport e f h a) x

theorem subgroupTransportIso_inv_pointsEquiv (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (hk : (subgroup i a).IsRepresentedBy k)
    (hk' : (subgroup j (characterLattice.congr e a)).IsRepresentedBy k')
    {U : Over B} (x : U ⟶ K'.X) :
    hk.pointsEquiv U (x ≫ (subgroupTransportIso e f h a hk hk').inv.hom.hom) =
      (subgroupTransportEquiv e f h a U).symm (hk'.pointsEquiv U x) := by
  apply Subtype.ext
  exact hk.isoOfComap_inv_points hk' f (subgroup_comap_of_transport e f h a) x

/-- The same ambient isomorphism restricts to supplied representatives of
centralizers of the full scheme-theoretic character kernels. -/
def kernelCentralizerTransportIso (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (hk : (kernelCentralizer i a).IsRepresentedBy k)
    (hk' : (kernelCentralizer j (characterLattice.congr e a)).IsRepresentedBy k') :
    K ≅ K' :=
  hk.isoOfComap hk' f (kernelCentralizer_comap_of_transport e f h a)

@[reassoc] theorem kernelCentralizerTransportIso_hom_comp (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (hk : (kernelCentralizer i a).IsRepresentedBy k)
    (hk' : (kernelCentralizer j (characterLattice.congr e a)).IsRepresentedBy k') :
    (kernelCentralizerTransportIso e f h a hk hk').hom ≫ k' = k ≫ f.hom :=
  hk.isoOfComap_hom_comp hk' f (kernelCentralizer_comap_of_transport e f h a)

@[reassoc] theorem kernelCentralizerTransportIso_inv_comp (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (hk : (kernelCentralizer i a).IsRepresentedBy k)
    (hk' : (kernelCentralizer j (characterLattice.congr e a)).IsRepresentedBy k') :
    (kernelCentralizerTransportIso e f h a hk hk').inv ≫ k = k' ≫ f.inv :=
  hk.isoOfComap_inv_comp hk' f (kernelCentralizer_comap_of_transport e f h a)

/-- The represented centralizer isomorphism has the full-kernel centralizer
point equivalence as its action on every test. -/
theorem kernelCentralizerTransportIso_pointsEquiv (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (hk : (kernelCentralizer i a).IsRepresentedBy k)
    (hk' : (kernelCentralizer j (characterLattice.congr e a)).IsRepresentedBy k')
    {U : Over B} (x : U ⟶ K.X) :
    hk'.pointsEquiv U (x ≫ (kernelCentralizerTransportIso e f h a hk hk').hom.hom.hom) =
      kernelCentralizerTransportEquiv e f h a U (hk.pointsEquiv U x) := by
  apply Subtype.ext
  exact hk.isoOfComap_hom_points hk' f (kernelCentralizer_comap_of_transport e f h a) x

theorem kernelCentralizerTransportIso_inv_pointsEquiv (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (hk : (kernelCentralizer i a).IsRepresentedBy k)
    (hk' : (kernelCentralizer j (characterLattice.congr e a)).IsRepresentedBy k')
    {U : Over B} (x : U ⟶ K'.X) :
    hk.pointsEquiv U (x ≫ (kernelCentralizerTransportIso e f h a hk hk').inv.hom.hom) =
      (kernelCentralizerTransportEquiv e f h a U).symm (hk'.pointsEquiv U x) := by
  apply Subtype.ext
  exact hk.isoOfComap_inv_points hk' f (kernelCentralizer_comap_of_transport e f h a) x

section Conjugation

variable {jG : S'.toGrp ⟶ G} {kG : K' ⟶ G}

/-- The represented root subgroup isomorphism uses the same actual point as
the supplied transporter square. -/
def subgroupTransporterConjIso (e : S ≅ S') (g : Over.mk (𝟙 B) ⟶ G.X)
    (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ jG)
    (a : characterLattice S) (hk : (subgroup i a).IsRepresentedBy k)
    (hkG : (subgroup jG (characterLattice.congr e a)).IsRepresentedBy kG) : K ≅ K' :=
  subgroupTransportIso e (G.innerIso g) h a hk hkG

theorem subgroupTransporterConjIso_hom_points (e : S ≅ S')
    (g : Over.mk (𝟙 B) ⟶ G.X)
    (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ jG)
    (a : characterLattice S) (hk : (subgroup i a).IsRepresentedBy k)
    (hkG : (subgroup jG (characterLattice.congr e a)).IsRepresentedBy kG)
    {U : Over B} (x : U ⟶ K.X) :
    (x ≫ (subgroupTransporterConjIso e g h a hk hkG).hom.hom.hom) ≫ kG.hom.hom =
      G.constantPoint g U * (x ≫ k.hom.hom) * (G.constantPoint g U)⁻¹ := by
  calc
    _ = (x ≫ k.hom.hom) ≫ (G.innerIso g).hom.hom.hom :=
      hk.isoOfComap_hom_points hkG (G.innerIso g)
        (subgroup_comap_of_transport e (G.innerIso g) h a) x
    _ = _ := comp_innerIso_hom G g U (x ≫ k.hom.hom)

theorem subgroupTransporterConjIso_inv_points (e : S ≅ S')
    (g : Over.mk (𝟙 B) ⟶ G.X)
    (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ jG)
    (a : characterLattice S) (hk : (subgroup i a).IsRepresentedBy k)
    (hkG : (subgroup jG (characterLattice.congr e a)).IsRepresentedBy kG)
    {U : Over B} (x : U ⟶ K'.X) :
    (x ≫ (subgroupTransporterConjIso e g h a hk hkG).inv.hom.hom) ≫ k.hom.hom =
      (G.constantPoint g U)⁻¹ * (x ≫ kG.hom.hom) * G.constantPoint g U := by
  calc
    _ = (x ≫ kG.hom.hom) ≫ (G.innerIso g).inv.hom.hom :=
      hk.isoOfComap_inv_points hkG (G.innerIso g)
        (subgroup_comap_of_transport e (G.innerIso g) h a) x
    _ = _ := by
      rw [← innerIso_inv_hom, comp_innerIso_hom, constantPoint_inv, inv_inv]

/-- The same transporting point identifies the represented full-kernel
centralizers, without a smoothness restriction on the kernels. -/
def kernelCentralizerTransporterConjIso (e : S ≅ S') (g : Over.mk (𝟙 B) ⟶ G.X)
    (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ jG)
    (a : characterLattice S) (hk : (kernelCentralizer i a).IsRepresentedBy k)
    (hkG : (kernelCentralizer jG (characterLattice.congr e a)).IsRepresentedBy kG) :
    K ≅ K' :=
  kernelCentralizerTransportIso e (G.innerIso g) h a hk hkG

theorem kernelCentralizerTransporterConjIso_hom_points (e : S ≅ S')
    (g : Over.mk (𝟙 B) ⟶ G.X)
    (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ jG)
    (a : characterLattice S) (hk : (kernelCentralizer i a).IsRepresentedBy k)
    (hkG : (kernelCentralizer jG (characterLattice.congr e a)).IsRepresentedBy kG)
    {U : Over B} (x : U ⟶ K.X) :
    (x ≫ (kernelCentralizerTransporterConjIso e g h a hk hkG).hom.hom.hom) ≫ kG.hom.hom =
      G.constantPoint g U * (x ≫ k.hom.hom) * (G.constantPoint g U)⁻¹ := by
  calc
    _ = (x ≫ k.hom.hom) ≫ (G.innerIso g).hom.hom.hom :=
      hk.isoOfComap_hom_points hkG (G.innerIso g)
        (kernelCentralizer_comap_of_transport e (G.innerIso g) h a) x
    _ = _ := comp_innerIso_hom G g U (x ≫ k.hom.hom)

theorem kernelCentralizerTransporterConjIso_inv_points (e : S ≅ S')
    (g : Over.mk (𝟙 B) ⟶ G.X)
    (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ jG)
    (a : characterLattice S) (hk : (kernelCentralizer i a).IsRepresentedBy k)
    (hkG : (kernelCentralizer jG (characterLattice.congr e a)).IsRepresentedBy kG)
    {U : Over B} (x : U ⟶ K'.X) :
    (x ≫ (kernelCentralizerTransporterConjIso e g h a hk hkG).inv.hom.hom) ≫ k.hom.hom =
      (G.constantPoint g U)⁻¹ * (x ≫ kG.hom.hom) * G.constantPoint g U := by
  calc
    _ = (x ≫ kG.hom.hom) ≫ (G.innerIso g).inv.hom.hom :=
      hk.isoOfComap_inv_points hkG (G.innerIso g)
        (kernelCentralizer_comap_of_transport e (G.innerIso g) h a) x
    _ = _ := by
      rw [← innerIso_inv_hom, comp_innerIso_hom, constantPoint_inv, inv_inv]

end Conjugation

end Langlands.GroupScheme.RelativeRoot
