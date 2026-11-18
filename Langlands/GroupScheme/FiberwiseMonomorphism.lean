import Langlands.GroupScheme.KernelPresentation
import Langlands.GroupScheme.TrivialFibres

/-! # Detecting monomorphisms of group schemes on residue-field fibres -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The canonical kernel-to-base isomorphism determined by monomorphisms on every
residue-field fibre. Its forward map is the kernel structure map. -/
noncomputable def kernelBaseIsoOfResidueFieldMonos {S : Scheme.{u}} {H G : GroupScheme S}
    (f : H ⟶ G) [LocallyOfFinitePresentation H.X.hom]
    (hbase : IsLocallyNoetherian S ∨ LocallyOfFiniteType G.X.hom)
    (hf : ∀ s : S, Mono ((GroupScheme.baseChange (S.fromSpecResidueField s)).map f).hom.hom) :
    (kernel f).X.left ≅ S := by
  have : LocallyOfFinitePresentation (kernel f).X.hom :=
    locallyOfFinitePresentation_kernel_of_source f hbase
  exact residueFieldTrivialityIso (kernel f) fun s =>
    (baseChange_kernel_hom_isIso_iff (S.fromSpecResidueField s) f).mpr (hf s)

@[simp]
theorem kernelBaseIsoOfResidueFieldMonos_hom {S : Scheme.{u}} {H G : GroupScheme S}
    (f : H ⟶ G) [LocallyOfFinitePresentation H.X.hom]
    (hbase : IsLocallyNoetherian S ∨ LocallyOfFiniteType G.X.hom)
    (hf : ∀ s : S, Mono ((GroupScheme.baseChange (S.fromSpecResidueField s)).map f).hom.hom) :
    (kernelBaseIsoOfResidueFieldMonos f hbase hf).hom = (kernel f).X.hom := rfl

/-- A homomorphism from a locally finitely presented group scheme is monomorphic if
all its residue-field fibres are monomorphic, provided either the base is locally
noetherian or the target is locally of finite type. No separatedness is assumed. -/
theorem mono_of_residueField_fibres {S : Scheme.{u}} {H G : GroupScheme S}
    (f : H ⟶ G) [LocallyOfFinitePresentation H.X.hom]
    (hbase : IsLocallyNoetherian S ∨ LocallyOfFiniteType G.X.hom)
    (hf : ∀ s : S, Mono ((GroupScheme.baseChange (S.fromSpecResidueField s)).map f).hom.hom) :
    Mono f.hom.hom := by
  have : LocallyOfFinitePresentation (kernel f).X.hom :=
    locallyOfFinitePresentation_kernel_of_source f hbase
  have : IsIso (kernel f).X.hom :=
    isIso_hom_of_residueField_fibres (kernel f) fun s =>
      (baseChange_kernel_hom_isIso_iff (S.fromSpecResidueField s) f).mpr (hf s)
  exact mono_of_kernel_hom_isIso f

end Langlands.GroupScheme
