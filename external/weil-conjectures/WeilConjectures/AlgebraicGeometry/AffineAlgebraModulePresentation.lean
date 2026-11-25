/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleGenerators
import WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleKernel
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Algebra-module presentations on an affine open

Source: Stacks Project, Morphisms, Lemma 0H88, proof, second paragraph;
EGA I, Proposition 9.6.1
(blueprint: lem-weil-pbc-affine-algebra-module-presentation).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- A module over a quasi-coherent algebra has a global algebra-module presentation on
an affine open whenever its underlying structure-sheaf module is quasi-coherent there.
The conclusion is a presentation on the slice site, rather than quasi-coherence on S.

Source: Stacks Project, Morphisms, Lemma 0H88, proof, second paragraph;
EGA I, Proposition 9.6.1
(blueprint: lem-weil-pbc-affine-algebra-module-presentation).

Proof:
1. Identify the affine open U with Spec R, where R = O_S(U). Put B = A(U) and M = G(U).
The algebra action makes M a B-module, and its restricted R-action is exactly the action
on sections of the underlying structure-sheaf module. Quasi-coherence of A and of the
underlying G on U identifies their restrictions with the tildes of B and M by the
counit of the tilde/global-sections adjunction.
2. Use all elements of M as generators. The B-linear map from the direct sum of copies
of B indexed by M to M, sending the generator indexed by m to m, is surjective. Use
all elements of its kernel as relations, obtaining a free B-module presentation.
3. A section m on U defines an A|U-linear map from A|U to G|U by a ↦ a m after restriction
to each smaller open. The action commutes with restriction, so these maps are morphisms
of module sheaves. Their coproduct gives the generator map. Each kernel element has
finite support and similarly gives a relation map into the generator free module.
4. Restriction of scalars preserves direct sums and cokernels: both module categories'
forgetful functors to abelian sheaves preserve these colimits and reflect isomorphisms.
Restriction to an open also preserves colimits. Thus the underlying free algebra-module
sheaves identify with the tildes of the corresponding direct sums of copies of B.
5. Under these identifications the generator and relation maps are the tildes of the
maps of step 2. Check this on global sections after the adjunction unit: the images of
the standard generators are m and the finite sums specified by the kernel elements.
The adjunction makes this check determine the maps on sheaves. Since tilde preserves
cokernels, the resulting sequence is a cokernel sequence as O_U-modules.
6. The forgetful functors to abelian sheaves also preserve kernels and reflect exactness,
so the sequence is a cokernel sequence as A|U-modules. Apply
SheafOfModules.presentationOfIsCokernelFree, and transport from the open subspace to the
slice site Over U by its canonical equivalence. This gives the stated presentation. -/
theorem nonempty_algebraModule_presentation_over (S : Scheme.{u})
    (A : S.CommAlgebraSheaf) (hA : A.toModule.IsQuasicoherent)
    (G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).obj
        A.right)) (U : S.Opens) (hU : IsAffineOpen U)
    (hG : (((SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).map
        A.hom)).obj G).over U).IsQuasicoherent) :
    Nonempty (G.over U).Presentation := by
  obtain ⟨generators⟩ :=
    nonempty_affine_algebraModule_generatingSections S A U hU (G.over U) hG
  have hK := affine_algebraModule_kernel_isQuasicoherent
    S A U (G.over U) hA hG generators.I generators.π
  obtain ⟨relations⟩ := nonempty_affine_algebraModule_generatingSections
    S A U hU (Limits.kernel generators.π) hK
  exact ⟨⟨generators, relations⟩⟩

end AlgebraicGeometry.Scheme.Modules
