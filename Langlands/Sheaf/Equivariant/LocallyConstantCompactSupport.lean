import Langlands.Sheaf.Equivariant.LocallyConstant
import Langlands.Sheaf.Equivariant.LocalSupport
import Langlands.Representation.LocallyConstant.CompactSupport
import Langlands.Representation.Smooth.Transfer.SubquotientProof

/-! # Compact sections of the full locally constant equivariant sheaf -/

noncomputable section

universe u v r w

namespace Langlands.Sheaf.Equivariant.LocallyConstantSheaf.CompactSections

open CategoryTheory TopologicalSpace Opposite Topology

namespace FunctionModule

export Langlands.CompactAction.LocallyConstantModule.CompactSupport
  (Functions representation coefficientIntertwiner representation_isSmooth coefficientFunctor)

end FunctionModule

variable {R : Type r} [CommRing R] {G : Type v} [Group G]
  {X : Type u} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  {M : Type w} [AddCommGroup M] [Module R M]

/-- The actual ordinary locally constant sheaf underlying the labelled presheaf. -/
abbrev ordinary (ρ : Representation R G M) :=
  LocalCompactSections.ordinary (presheaf (X := X) ρ)

/-- The original representation on every compactly supported sheaf section. -/
abbrev representation (ρ : Representation R G M) :=
  LocalCompactSections.representation (presheaf (X := X) ρ)

/-- The original restriction evaluates to the original function on the named open. -/
theorem restrict_apply (ρ : Representation R G M) (U : Opens X)
    (f : LocallyConstant X M) (y : U) :
    LocallyConstant.toFun
      (Langlands.Sheaf.LocalSupport.restrict (ordinary ρ) U
        (globalSectionsLinearEquiv ρ f)) y = f y.val := by
  change ρ (1 : G)⁻¹ (f ((1 : G) • y.val)) = f y.val
  simp

/-- Local vanishing of the actual section is equivalent to zero at the point. -/
theorem vanishesNear_iff (ρ : Representation R G M) (f : LocallyConstant X M) (x : X) :
    Langlands.Sheaf.LocalSupport.VanishesNear (ordinary ρ)
        (globalSectionsLinearEquiv ρ f) x ↔ f x = 0 := by
  constructor
  · rintro ⟨U, hxU, hU⟩
    have h := congrArg (fun s : LocallyConstant U M => s ⟨x, hxU⟩) hU
    change LocallyConstant.toFun
      (Langlands.Sheaf.LocalSupport.restrict (ordinary ρ) U
        (globalSectionsLinearEquiv ρ f)) ⟨x, hxU⟩ = 0 at h
    exact (restrict_apply ρ U f ⟨x, hxU⟩).symm.trans h
  · intro hx
    let U : Opens X := ⟨{y | f y = 0}, f.isLocallyConstant.isOpen_fiber 0⟩
    refine ⟨U, hx, ?_⟩
    apply LocallyConstant.ext
    intro y
    exact (restrict_apply ρ U f y).trans y.property

/-- Sheaf support is the actual nonzero support of the original function. -/
theorem support_eq_functionSupport (ρ : Representation R G M) (f : LocallyConstant X M) :
    Langlands.Sheaf.LocalSupport.support (ordinary ρ) (globalSectionsLinearEquiv ρ f) =
      Function.support f := by
  ext x
  exact not_congr (vanishesNear_iff ρ f x)

/-- Local constancy makes this function support closed, so it equals topological support. -/
theorem support_eq_tsupport (ρ : Representation R G M) (f : LocallyConstant X M) :
    Langlands.Sheaf.LocalSupport.support (ordinary ρ) (globalSectionsLinearEquiv ρ f) =
      tsupport f := by
  rw [tsupport, ← support_eq_functionSupport ρ f]
  exact (Langlands.Sheaf.LocalSupport.isClosed_support (ordinary (X := X) ρ)
    (globalSectionsLinearEquiv ρ f)).closure_eq.symm

/-- The original whole-space linear equivalence restricts to all compact sections. -/
def linearEquiv (ρ : Representation R G M) :
    FunctionModule.Functions R X M ≃ₗ[R]
      Langlands.Sheaf.LocalSupport.submodule (ordinary (X := X) ρ) where
  toFun f := ⟨globalSectionsLinearEquiv ρ f.val, by
    change IsCompact (Langlands.Sheaf.LocalSupport.support (ordinary ρ) _)
    rw [support_eq_tsupport]
    exact f.property⟩
  invFun s := ⟨(globalSectionsLinearEquiv ρ).symm s.val, by
    change IsCompact (tsupport _)
    rw [← support_eq_tsupport ρ]
    exact (congrArg (fun t =>
      IsCompact (Langlands.Sheaf.LocalSupport.support (ordinary (X := X) ρ) t))
      ((globalSectionsLinearEquiv (X := X) ρ).apply_symm_apply s.val)).mpr s.property⟩
  left_inv f := Subtype.ext ((globalSectionsLinearEquiv ρ).symm_apply_apply f.val)
  right_inv s := Subtype.ext ((globalSectionsLinearEquiv ρ).apply_symm_apply s.val)
  map_add' f h := Subtype.ext ((globalSectionsLinearEquiv ρ).map_add f.val h.val)
  map_smul' a f := Subtype.ext ((globalSectionsLinearEquiv ρ).map_smul a f.val)

@[simp]
theorem linearEquiv_apply (ρ : Representation R G M) (f : FunctionModule.Functions R X M) :
    (linearEquiv ρ f).val = globalSectionsLinearEquiv ρ f.val := rfl

/-- This is the restriction of the already proved global-section equivariance. -/
theorem linearEquiv_equivariant (ρ : Representation R G M) (g : G)
    (f : FunctionModule.Functions R X M) :
    linearEquiv ρ (FunctionModule.representation ρ g f) =
      representation ρ g (linearEquiv ρ f) := by
  apply Subtype.ext
  exact globalSectionsLinearEquiv_equivariant ρ g f.val

/-- Actual compact sheaf sections and compact functions are equivariantly linearly equivalent. -/
def equiv (ρ : Representation R G M) :
    (FunctionModule.representation (X := X) ρ).Equiv (representation (X := X) ρ) :=
  Representation.Equiv.mk (linearEquiv ρ) (fun g =>
    LinearMap.ext (linearEquiv_equivariant ρ g))

/-- The resulting isomorphism is in the actual algebraic representation category. -/
def repIso (ρ : Representation R G M) :
    Rep.of (FunctionModule.representation (X := X) ρ) ≅ Rep.of (representation (X := X) ρ) :=
  Rep.mkIso (equiv ρ)

variable (R G X)

/-- The compact function construction is functorial in arbitrary algebraic coefficients. -/
def functionFunctor : Rep.{w} R G ⥤ Rep.{max u w} R G where
  obj P := Rep.of (FunctionModule.representation (X := X) P.ρ)
  map a := Rep.ofHom (FunctionModule.coefficientIntertwiner (X := X) a.hom)
  map_id _ := by ext f; rfl
  map_comp _ _ := by ext f; rfl

/-- Construct the full sheaf first, then take its actual compact sections. -/
def sectionsFunctor : Rep.{w} R G ⥤ Rep.{max u w} R G :=
  LocallyConstantSheaf.functor R G X ⋙ LocalCompactSections.functor R G X

/-- The actual compact-section identification is natural in all coefficient maps. -/
def comparison : functionFunctor R G X ≅ sectionsFunctor R G X :=
  NatIso.ofComponents (fun P => repIso (X := X) P.ρ) (by
    intro P Q a
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    rfl)

variable {R G X}
variable [TopologicalSpace G] [IsTopologicalGroup G] [ContinuousSMul G X]

/-- Every compact sheaf section is smooth for smooth coefficients and a continuous action. -/
theorem representation_isSmooth (ρ : Representation R G M) (hρ : Langlands.IsSmooth ρ) :
    Langlands.IsSmooth (representation (X := X) ρ) :=
  Langlands.isSmooth_of_surjective (equiv ρ).toIntertwiningMap
    (linearEquiv ρ).surjective (FunctionModule.representation_isSmooth ρ hρ)

/-- Bundle the full compact-section representation with its derived smoothness. -/
def smoothSections (A : Langlands.SmoothRep.{r, v, w} R G) :
    Langlands.SmoothRep.{r, v, max u w} R G :=
  Langlands.SmoothRep.of (representation (X := X) A.representation)
    (representation_isSmooth A.representation A.isSmooth)

/-- Smooth coefficient maps act through the original full sheaf and compact-section maps. -/
def smoothMap {A B : Langlands.SmoothRep.{r, v, w} R G} (a : A ⟶ B) :
    smoothSections (X := X) A ⟶ smoothSections (X := X) B :=
  Langlands.SmoothRep.ofHom (LocalCompactSections.map
    (LocallyConstantSheaf.map (X := X) a.hom).hom)

variable (R G X)

/-- The constructed whole compact-section representations form a smooth coefficient functor. -/
def smoothFunctor :
    Langlands.SmoothRep.{r, v, w} R G ⥤ Langlands.SmoothRep.{r, v, max u w} R G where
  obj := smoothSections (X := X)
  map := smoothMap
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    rfl

/-- The comparison identifies the entire smooth compact-section modules naturally. -/
def smoothComparison :
    FunctionModule.coefficientFunctor (R := R) (G := G) (X := X) ≅ smoothFunctor R G X :=
  NatIso.ofComponents (fun A =>
    Langlands.SmoothRep.mkIso (equiv (X := X) A.representation)) (by
      intro A B a
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      apply LocallyConstant.ext
      intro x
      rfl)

end Langlands.Sheaf.Equivariant.LocallyConstantSheaf.CompactSections
