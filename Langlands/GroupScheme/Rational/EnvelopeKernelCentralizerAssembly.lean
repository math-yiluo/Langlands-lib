import Langlands.GroupScheme.Rational.EnvelopeCentralizerGeometry
import Langlands.GroupScheme.Rational.FiniteFieldEnvelopeKernelNormality

/-! # Constructing the actual kernel-centralizer geometry of a torus envelope -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace TorusGeneratedEnvelope

/-- A supplied sectioned torus quotient determines all the actual kernel,
centralizer and intersection presentations required by the finite-field
normality criterion. -/
def kernelCentralizerGeometry
    {k : Type u} [Field k] [PerfectField k]
    {G N : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (D : TorusGeneratedEnvelope G)
    [Smooth D.group.X.hom] [ConnectedSpace D.group.X.left]
    (n : N ⟶ G) (hn : IsClosedSubgroup n) (hN : IsUnipotent N)
    (q : G ⟶ T.toGrp)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)
    (s : T.toGrp ⟶ G) (hs : s ≫ q = 𝟙 T.toGrp) (hT : IsTorus T.toGrp) :
    EnvelopeKernelCentralizerGeometry D n q s := by
  let : IsClosedImmersion n.hom.hom.left := hn
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom N.X.hom := by
    rw [← n.hom.hom.w]
    infer_instance
  let : LocallyOfFiniteType N.X.hom := by
    rw [← n.hom.hom.w]
    infer_instance
  let : IsClosedImmersion D.inclusion.hom.hom.left := D.closed
  let : Mono D.inclusion.hom.hom := D.represents.1
  let : IsAffineHom D.group.X.hom := D.isAffineHom
  have hsclosed : IsClosedSubgroup s := IsClosedSubgroup.of_comp_eq_id s q hs
  let : IsClosedImmersion s.hom.hom.left := hsclosed
  let : IsAffineHom T.X.hom := by
    rw [← s.hom.hom.w]
    infer_instance
  let : Smooth T.X.hom := hT.smooth
  let sH := D.torusFactor s hT hsclosed
  have hsHcomp : sH ≫ D.inclusion = s := D.torusFactor_comp s hT hsclosed
  have hsH : sH ≫ (D.inclusion ≫ q) = 𝟙 T.toGrp :=
    D.torusFactor_section q s hT hsclosed hs
  have hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range n :=
    hq.2.2.2
  let V := kernel (D.inclusion ≫ q)
  let v : V ⟶ D.group := kernelι (D.inclusion ≫ q)
  let m : V ⟶ N := SectionedSubgroupKernel.toAmbientKernel D.inclusion n q hker
  have hm : m ≫ n = v ≫ D.inclusion :=
    SectionedSubgroupKernel.toAmbientKernel_comp D.inclusion n q hker
  have hvclosed : IsClosedSubgroup v :=
    inferInstanceAs (IsClosedImmersion (kernelι (D.inclusion ≫ q)).hom.hom.left)
  have hVgeom := SectionedSubgroupKernel.smooth_connected D.inclusion q sH hsH
  let : Smooth V.X.hom := hVgeom.1
  let : ConnectedSpace V.X.left := hVgeom.2
  let : IsAffineHom V.X.hom := SectionedSubgroupKernel.isAffineHom D.inclusion q
  have hV : IsUnipotent V :=
    SectionedSubgroupKernel.isUnipotent D.inclusion n q hker D.closed hn hN
  let C : TorusKernelCentralizerData (sH ≫ D.inclusion) n :=
    torusKernelCentralizerData q (sH ≫ D.inclusion) hT
      (by rwa [hsHcomp]) (by rwa [hsHcomp]) n hker hn hN
  let E : TorusKernelCentralizerData sH v :=
    torusKernelCentralizerData (D.inclusion ≫ q) sH hT
      (D.torusFactor_closed s hT hsclosed) hsH v rfl hvclosed hV
  have hEgeom := TorusKernelCentralizerData.intersection_geometry
    sH D.inclusion v m n hm C E
  exact {
    kernel := V
    inclusion := v
    closed := hvclosed
    toKernel := m
    toKernel_comp := hm
    smooth := hVgeom.1
    connected := hVgeom.2
    unipotent := hV
    split := perfectFieldUnipotentSplit k V hVgeom.2 hV
    quotient := SectionedSubgroupKernel.isFppfQuotient D.inclusion q sH hsH
    centralizer := C.group
    centralizerInclusion := C.inclusion
    centralizerClosed := C.isClosedSubgroup
    representsCentralizer := by simpa only [hsHcomp] using C.represents
    centralizerSmooth := C.smooth
    centralizerConnected := C.connectedSpace
    centralizerSplit := C.isSplitUnipotent
    intersectionSmooth := hEgeom.1
    intersectionConnected := hEgeom.2.2.1
    intersectionSplit := TorusKernelCentralizerData.intersection_isSplitUnipotent
      sH D.inclusion v m n hm C E
  }

/-- The geometry record uses the original radical and unchanged quotient of
a supplied sectioned geometric-radical torus quotient. -/
def sectionedQuotientKernelCentralizerGeometry
    {k : Type u} [Field k] [PerfectField k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (D : TorusGeneratedEnvelope G)
    [Smooth D.group.X.hom] [ConnectedSpace D.group.X.left]
    (a : SplitGeometricRadicalSectionedTorusQuotient G) :
    EnvelopeKernelCentralizerGeometry (T := a.torus) D a.inclusion
      a.quotientData.projection a.quotientData.sectionHom :=
  D.kernelCentralizerGeometry a.inclusion
    a.isGeometricUnipotentRadical.1.isClosedSubgroup
    a.isGeometricUnipotentRadical.1.isUnipotent
    a.quotientData.projection a.quotientData.isFppfQuotient
    a.quotientData.sectionHom a.quotientData.sectionHom_comp a.torus_isTorus

end TorusGeneratedEnvelope

end Langlands.GroupScheme
