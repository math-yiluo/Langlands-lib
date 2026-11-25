/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsOpenLift
import WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting

/-! # Local lifting of tensor sections of an epimorphism

Source: Stacks Project, Tags 070S(2), 03FH(1), and 0096.
(blueprint: lem-sc-etale-tensor-sections-local-surjectivity)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] tensorPullback tensorPullbackObj

/-- Tensor sections of a module epimorphism are locally surjective on the small etale site.
Source: Stacks Project, Descent, Tag 070S(2), and Tag 03FH(1); pullback adjunction
Tag 0096. (blueprint: lem-sc-etale-tensor-sections-local-surjectivity)

Proof: Fix an etale object U and a section of the pullback of H. Tensor pullback
along U to X is a left adjoint, hence takes the epimorphism psi to an epimorphism
of module sheaves on U. Such an epimorphism is locally surjective: its cokernel
is the sheafification of the sectionwise cokernel, so each section of the target
has lifts on a Zariski covering of U. View each open in that covering as an etale
object over X. Pullback along its open immersion agrees with restriction of the
module sheaf. Under this identification, the unit-normalized composition maps
in the tensor-section presheaf identify those lifts with lifts of the restriction
of the original section. Naturality identifies their images under beta with that
restriction. Thus the image sieve contains this etale covering sieve and is
covering. Lifting and lowering a section through ULift does not change its image
sieve. Empty objects and zero modules obey the same local criterion. No
quasi-coherence or flatness is needed. -/
theorem etaleTensorSections_locallySurjective {X : Scheme.{u}} {G H : X.Modules}
    (ψ : G ⟶ H) [Epi ψ]
    (β : etaleTensorSectionsPresheaf G ⟶ etaleTensorSectionsPresheaf H)
    (hβ : ∀ U : X.Etaleᵒᵖ, β.app U = ((tensorPullback U.unop.hom).map ψ).app ⊤) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (Functor.whiskerRight β AddCommGrpCat.uliftFunctor.{u + 1, u}) := by
  classical
  constructor
  intro U s
  let A := tensorPullback U.hom
  let adj := Classical.choose (exists_tensorPullbackAdjunction U.hom)
  have : A.IsLeftAdjoint := adj.isLeftAdjoint
  have : Epi (A.map ψ) := inferInstance
  have hl := ((RingedSpace.module_exactness_local_lifting U.left.toRingedSpace).2.1
    (A.obj G) (A.obj H) (A.map ψ)).2.mpr inferInstance
  obtain ⟨I, V, hV, t, hcover, ht⟩ := hl ⊤ s.down
  let Z : I → X.Etale := fun i ↦
    Scheme.Etale.mk (Scheme.Opens.ι (show U.left.Opens from V i) ≫ U.hom)
  let f : ∀ i, Z i ⟶ U := fun i ↦
    MorphismProperty.Over.homMk (Scheme.Opens.ι (show U.left.Opens from V i)) rfl
  have hmem : Sieve.ofArrows Z f ∈ X.smallEtaleTopology U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⨆ i, V i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨i, ⟨⟨x, hi⟩, rfl⟩⟩
  apply X.smallEtaleTopology.superset_covering _ hmem
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  obtain ⟨z, hz⟩ := etaleTensorSections_open_lift ψ U (V i) s.down (t i) (ht i)
  refine ⟨ULift.up z, ?_⟩
  apply ULift.ext
  change β.app (op (Z i)) z = (etaleTensorSectionsPresheaf H).map (f i).op s.down
  rw [hβ]
  exact hz

end
end AlgebraicGeometry.Scheme.Modules
