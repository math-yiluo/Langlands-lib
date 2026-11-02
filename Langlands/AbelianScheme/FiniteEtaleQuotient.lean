import Langlands.AbelianScheme.Basic
import Langlands.AbelianScheme.IsogenySpecialization
import Langlands.AbelianScheme.Kernel
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Quotient data of abelian schemes by finite étale subgroup schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

variable {S : Scheme.{u}}

/-- A finite étale closed subgroup scheme of an abelian scheme: an actual commutative
group scheme with a homomorphism into `A` that is a closed immersion of schemes, whose
structure morphism to the base is finite and étale. -/
structure FiniteEtaleSubgroup (A : AbelianScheme S) where
  /-- The subgroup scheme, retained as an actual commutative group scheme over `S`. -/
  G : CommGroupScheme S
  /-- The inclusion, an actual homomorphism of commutative group schemes. -/
  inclusion : G ⟶ A.toCommGroupScheme
  [isClosedImmersion : IsClosedImmersion (CommGroupScheme.hom inclusion)]
  [isFinite : IsFinite G.X.hom]
  [etale : Etale G.X.hom]

attribute [instance] FiniteEtaleSubgroup.isClosedImmersion FiniteEtaleSubgroup.isFinite
  FiniteEtaleSubgroup.etale

namespace FiniteEtaleSubgroup

variable {A : AbelianScheme S}

/-- Quotient data for a finite étale closed subgroup `K` of `A`: an abelian scheme `B`
and a finite étale surjective homomorphism `q : A ⟶ B` whose scheme kernel is exactly `K`,
expressed by the cartesian square of `K ⟶ A` against the unit section of `B`. -/
structure QuotientData (K : FiniteEtaleSubgroup A) where
  /-- The quotient abelian scheme. -/
  B : AbelianScheme S
  /-- The quotient homomorphism. -/
  q : A ⟶ B
  [isFinite : IsFinite (AbelianScheme.hom q)]
  [etale : Etale (AbelianScheme.hom q)]
  [surjective : Surjective (AbelianScheme.hom q)]
  /-- `K` is the fibre product of `q` and the unit section of `B`. -/
  isPullback : IsPullback (CommGroupScheme.hom K.inclusion) K.G.X.hom (AbelianScheme.hom q) η[B.X].left

attribute [instance] QuotientData.isFinite QuotientData.etale QuotientData.surjective

namespace QuotientData

variable {K : FiniteEtaleSubgroup A} (D : K.QuotientData)

/-- The quotient morphism is flat, since étale morphisms are smooth and hence flat. -/
theorem flat : Flat (AbelianScheme.hom D.q) := inferInstance

/-- The quotient homomorphism is an isogeny in the finite-flat-surjective sense. -/
theorem isIsogeny : IsIsogeny D.q :=
  ⟨D.isFinite, D.flat, D.surjective⟩

/-- The scheme-level identification of `K` with the scheme kernel of `q`. -/
def kernelSchemeIso : K.G.X.left ≅ (GroupScheme.kernel (groupHom D.q)).X.left :=
  D.isPullback.isoIsPullback _ _ (GroupScheme.kernel_isPullback_scheme (groupHom D.q))

@[reassoc (attr := simp)]
theorem kernelSchemeIso_hom_inclusion :
    D.kernelSchemeIso.hom ≫ (GroupScheme.kernelι (groupHom D.q)).hom.hom.left =
      CommGroupScheme.hom K.inclusion :=
  IsPullback.isoIsPullback_hom_fst _ _ D.isPullback
    (GroupScheme.kernel_isPullback_scheme (groupHom D.q))

@[reassoc (attr := simp)]
theorem kernelSchemeIso_hom_structure :
    D.kernelSchemeIso.hom ≫ (GroupScheme.kernel (groupHom D.q)).X.hom = K.G.X.hom :=
  IsPullback.isoIsPullback_hom_snd _ _ D.isPullback
    (GroupScheme.kernel_isPullback_scheme (groupHom D.q))

/-- The identification of `K` with the scheme kernel of `q` as objects over `S`. -/
def kernelOverIso : K.G.X ≅ (GroupScheme.kernel (groupHom D.q)).X :=
  Over.isoMk D.kernelSchemeIso D.kernelSchemeIso_hom_structure

@[reassoc (attr := simp)]
theorem kernelOverIso_hom_inclusion :
    D.kernelOverIso.hom ≫ (GroupScheme.kernelι (groupHom D.q)).hom.hom =
      (CommGroupScheme.groupHom K.inclusion).hom.hom := by
  ext
  exact D.kernelSchemeIso_hom_inclusion

/-- The identification of `K` with the group-scheme kernel of `q`, compatible with the
inclusions into `A`. -/
def kernelIso : K.G.toGrp ≅ GroupScheme.kernel (groupHom D.q) :=
  Grp.mkIso D.kernelOverIso
    (by
      rw [← cancel_mono (GroupScheme.kernelι (groupHom D.q)).hom.hom, Category.assoc,
        kernelOverIso_hom_inclusion, IsMonHom.one_hom, IsMonHom.one_hom])
    (by
      rw [← cancel_mono (GroupScheme.kernelι (groupHom D.q)).hom.hom, Category.assoc,
        kernelOverIso_hom_inclusion, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
        ← Category.assoc, tensorHom_comp_tensorHom, kernelOverIso_hom_inclusion])

@[reassoc (attr := simp)]
theorem kernelIso_hom_inclusion :
    D.kernelIso.hom ≫ GroupScheme.kernelι (groupHom D.q) = CommGroupScheme.groupHom K.inclusion := by
  ext
  exact D.kernelSchemeIso_hom_inclusion

end QuotientData

/-- The scheme kernel of a finite étale homomorphism of abelian schemes, as a finite étale
closed subgroup of its source. -/
def ofKernel {B : AbelianScheme S} (q : A ⟶ B) [IsFinite (AbelianScheme.hom q)]
    [Etale (AbelianScheme.hom q)] : FiniteEtaleSubgroup A where
  G := { toGrp := GroupScheme.kernel (groupHom q) }
  inclusion := Additive.ofMul (GroupScheme.kernelι (groupHom q))
  isClosedImmersion := GroupScheme.kernelι_isClosedImmersion (groupHom q)
  isFinite := MorphismProperty.of_isPullback (P := @IsFinite)
    (GroupScheme.kernel_isPullback_scheme (groupHom q)) inferInstance
  etale := MorphismProperty.of_isPullback (P := @Etale)
    (GroupScheme.kernel_isPullback_scheme (groupHom q)) inferInstance

/-- A finite étale surjective homomorphism of abelian schemes is quotient data for its own
scheme kernel. -/
def QuotientData.ofKernel {B : AbelianScheme S} (q : A ⟶ B) [IsFinite (AbelianScheme.hom q)]
    [Etale (AbelianScheme.hom q)] [Surjective (AbelianScheme.hom q)] :
    (FiniteEtaleSubgroup.ofKernel q).QuotientData where
  B := B
  q := q
  isPullback := GroupScheme.kernel_isPullback_scheme (groupHom q)

end FiniteEtaleSubgroup

end Langlands.AbelianScheme
