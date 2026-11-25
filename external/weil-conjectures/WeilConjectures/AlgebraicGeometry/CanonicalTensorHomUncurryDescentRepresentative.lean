/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Existence of representative-normalized values, without isomorphism transport.
Source: Stacks Project, cohomology.tex, Tag 08DJ; sites-cohomology.tex,
Tags 0A90 and 0A96.
(blueprint: lem-pc-tensor-hom-uncurry-descent-representative).

Proof: First take K-flat Lc and the fixed K-injective resolution I(M).
Hom(Lc,I(M)) is K-injective by Tag 0A96. Thus maps in the derived category into
this complex lift uniquely to homotopy classes of chain maps. Choose a chain
map in that class, uncurry by the sheaf tensor-Hom adjunction on every tensor
summand, and localize the explicit coproduct extension. A chain homotopy gives
an uncurried homotopy: apply the same evaluation to its degree-minus-one
components. The differential calculation of Tag 0A90 identifies its boundary
with the difference of the uncurried maps. Hence the result is independent of
the lift. Tensor model comparisons and the inverse map to I(M) put it in the
stated derived Hom set. For arbitrary L, choose a K-flat resolution Lc to L.
Hom(-,I(M)) and P tensor - invert its quasi-isomorphism, and evaluation commutes
with that map. Cancel the localized comparison to obtain the required formula
for L itself. Common K-flat resolutions show that the values assigned by two
such descriptions of the same literal derived input agree. This defines the
required values on all inputs covered by the displayed equation; assign zero
to other inputs. No compatibility on those other inputs is claimed. Zero inputs
and zero complexes give zero, and the argument uses no boundedness. -/
theorem exists_tensorHomUncurry_descent_representative (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI := schemeDerivedTensorMonoidal X
    ∃ t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M),
      ∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsKFlatTensor →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            pullbackTensorModelMap X P L ≫
              DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
                schemeHomResolutionInverse X M := by
  classical
  let := schemeDerivedTensorMonoidal X
  let R (K L M : schemeDerivedCategory X)
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) (g : K ⊗ L ⟶ M) : Prop :=
    ∃ (P Lc Mc : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (hP : P.IsKFlatTensor)
      (φ : P ⟶ homComplex (R := X.sheaf) Lc
        ((schemeHomKInjectiveResolution X).obj Mc)),
      DerivedCategory.Q.obj P = K ∧ DerivedCategory.Q.obj Lc = L ∧
      DerivedCategory.Q.obj Mc = M ∧
      HEq (DerivedCategory.Q.map φ ≫
        (schemeDerivedInternalHomResolutionIso X Lc Mc).inv) f ∧
      HEq (pullbackTensorModelMap X P Lc ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P Lc Mc φ) ≫
          schemeHomResolutionInverse X Mc) g
  have unique (K L M : schemeDerivedCategory X) (f) (g g' : K ⊗ L ⟶ M)
      (hg : R K L M f g) (hg' : R K L M f g') : g = g' := by
    obtain ⟨P, Lc, Mc, hP, φ, hK, hL, hM, hφ, hψ⟩ := hg
    obtain ⟨P', Lc', Mc', hP', φ', hK', hL', hM', hφ', hψ'⟩ := hg'
    have h := tensorHomUncurry_representative_coherence X P Lc Mc P' Lc' Mc'
      hP hP' φ φ' (hK.trans hK'.symm) (hL.trans hL'.symm)
      (hM.trans hM'.symm) (hφ.trans hφ'.symm)
    exact eq_of_heq (hψ.symm.trans (h.trans hψ'))
  let t (K L M : schemeDerivedCategory X) (f) : K ⊗ L ⟶ M :=
    if h : ∃! g, R K L M f g then Classical.choose h else 0
  refine ⟨t, ?_⟩
  intro P L M hP φ
  let g := pullbackTensorModelMap X P L ≫
    DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
      schemeHomResolutionInverse X M
  have hg : R (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L)
      (DerivedCategory.Q.obj M)
      (DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso X L M).inv) g :=
    ⟨P, L, M, hP, φ, rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩
  have hex : ∃! g, R (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L)
      (DerivedCategory.Q.obj M)
      (DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso X L M).inv) g :=
    ⟨g, hg, fun g' hg' ↦ unique _ _ _ _ _ _ hg' hg⟩
  dsimp only [t]
  rw [dite_eq_left hex]
  exact unique _ _ _ _ _ g (Classical.choose_spec hex).1 hg

end AlgebraicGeometry
