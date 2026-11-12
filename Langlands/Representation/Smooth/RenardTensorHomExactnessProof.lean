import Langlands.Representation.Smooth.RenardTensorHomAdjunctionProof
import Langlands.Representation.CompactCoefficient.SemisimplicityProof
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Renard.Smooth.TensorHom

open TensorProduct MeasureTheory

universe u v a b c

section HomMaps

variable {R : Type*} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type a} {W : Type b} {U : Type c}
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]
variable (ρ : Representation R G V) (σ : Representation R G W) (τ : Representation R G U)

/-- Covariance of algebraic Hom. -/
def postcompose (f : σ.IntertwiningMap τ) :
    (Representation.linHom ρ σ).IntertwiningMap (Representation.linHom ρ τ) where
  toLinearMap :=
    { toFun := fun φ => f.toLinearMap.comp φ
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  isIntertwining' := by
    intro g
    ext φ x
    exact f.isIntertwining _ _ g _

/-- Contravariance of algebraic Hom. -/
def precompose (f : ρ.IntertwiningMap σ) :
    (Representation.linHom σ τ).IntertwiningMap (Representation.linHom ρ τ) where
  toLinearMap :=
    { toFun := fun φ => φ.comp f.toLinearMap
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  isIntertwining' := by
    intro g
    ext φ x
    change τ g (φ (σ g⁻¹ (f x))) = τ g (φ (f (ρ g⁻¹ x)))
    rw [f.isIntertwining]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Fixed Hom vectors are precisely intertwiners for the subgroup. -/
theorem hom_fixed_iff (K : Subgroup G) (f : V →ₗ[R] W) :
    f ∈ fixedVectors (Representation.linHom ρ σ) K ↔
      ∀ k : K, ∀ x, f (ρ k.val x) = σ k.val (f x) := by
  constructor
  · intro hf k x
    have h := congrArg (fun F : V →ₗ[R] W => F (ρ k.val x)) (hf k)
    simpa [Representation.linHom_apply] using h.symm
  · intro hf k
    apply LinearMap.ext
    intro x
    change σ k.val (f (ρ k.val⁻¹ x)) = f x
    rw [← hf k, ρ.self_inv_apply]

omit [IsTopologicalGroup G] in
/-- Smoothness of a diagonal tensor product follows from pure-tensor spanning. -/
theorem tensor_smooth (hρ : IsSmooth ρ) (hσ : IsSmooth σ) :
    IsSmooth (Representation.tprod ρ σ) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨K, hK⟩ := hρ x
    obtain ⟨L, hL⟩ := hσ y
    refine ⟨K ⊓ L, ?_⟩
    intro k
    change ρ k.val x ⊗ₜ σ k.val y = x ⊗ₜ y
    exact congrArg₂ (fun x y => x ⊗ₜ[R] y)
      (hK ⟨k.val, k.property.1⟩) (hL ⟨k.val, k.property.2⟩)
  | add x y hx hy => exact isSmoothVector_add hx hy

end HomMaps

section CompactSplitting

variable {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
variable {V : Type a} {W : Type b}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable (ρ : Representation ℂ K V) (σ : Representation ℂ K W)

/-- On a compact group every coefficient has compact support, so the published
compact-coefficient theorem supplies semisimplicity. -/
theorem compact_semisimple (hρ : IsSmooth ρ) :
    IsSemisimpleModule (MonoidAlgebra ℂ K) ρ.asModule := by
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  apply (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp
  apply CompactCoefficientSemisimplicity.isSemisimpleRepresentation_of_compactCoefficients
    (Measure.haar (G := K)) ρ hρ
  intro x ℓ _
  exact HasCompactSupport.of_compactSpace _

/-- An injective intertwiner of smooth compact-group representations splits. -/
theorem compact_retraction (hσ : IsSmooth σ) (i : ρ.IntertwiningMap σ)
    (hi : Function.Injective i) :
    ∃ r : σ.IntertwiningMap ρ, r.toLinearMap.comp i.toLinearMap = LinearMap.id := by
  let := compact_semisimple σ hσ
  let im := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ i
  obtain ⟨r, hr⟩ := IsSemisimpleModule.extension_property im hi
    (LinearMap.id : ρ.asModule →ₗ[MonoidAlgebra ℂ K] ρ.asModule)
  refine ⟨(Representation.IntertwiningMap.equivLinearMapAsModule σ ρ).symm r, ?_⟩
  ext x
  exact LinearMap.congr_fun hr x

/-- A surjective intertwiner of smooth compact-group representations splits. -/
theorem compact_section (hρ : IsSmooth ρ) (q : ρ.IntertwiningMap σ)
    (hq : Function.Surjective q) :
    ∃ s : σ.IntertwiningMap ρ, q.toLinearMap.comp s.toLinearMap = LinearMap.id := by
  let := compact_semisimple ρ hρ
  let qm := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ q
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property qm hq
    (LinearMap.id : σ.asModule →ₗ[MonoidAlgebra ℂ K] σ.asModule)
  refine ⟨(Representation.IntertwiningMap.equivLinearMapAsModule σ ρ).symm s, ?_⟩
  ext x
  exact LinearMap.congr_fun hs x

end CompactSplitting

section HomExactness

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable {V : Type a} {W : Type b} {U : Type c}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup U] [Module ℂ U]
variable (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (τ : Representation ℂ G U)

/-- A smooth linear map extends along every injective intertwiner of smooth sources. -/
theorem extend_smooth (hσ : IsSmooth σ) (i : ρ.IntertwiningMap σ)
    (hi : Function.Injective i) (f : V →ₗ[ℂ] U)
    (hf : f ∈ smoothVectors (Representation.linHom ρ τ)) :
    ∃ f' ∈ smoothVectors (Representation.linHom σ τ), f'.comp i.toLinearMap = f := by
  obtain ⟨H, hH⟩ := hf
  obtain ⟨K, hKH, hK, -⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ H
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  let ρK : Representation ℂ K V := ρ.comp K.toSubgroup.subtype
  let σK : Representation ℂ K W := σ.comp K.toSubgroup.subtype
  let τK : Representation ℂ K U := τ.comp K.toSubgroup.subtype
  let iK : ρK.IntertwiningMap σK :=
    { toLinearMap := i.toLinearMap
      isIntertwining' := fun k => i.isIntertwining' k.val }
  let fK : ρK.IntertwiningMap τK :=
    { toLinearMap := f
      isIntertwining' := by
        intro k
        ext x
        exact (hom_fixed_iff ρ τ H.toSubgroup f).mp hH ⟨k.val, hKH k.property⟩ x }
  obtain ⟨r, hr⟩ := compact_retraction ρK σK
    (isSmooth_comp _ continuous_subtype_val hσ) iK hi
  refine ⟨(fK.comp r).toLinearMap, ⟨K, ?_⟩, ?_⟩
  · exact (hom_fixed_iff σ τ K.toSubgroup _).mpr (fun k x => (fK.comp r).isIntertwining _ _ k x)
  · change (f.comp r.toLinearMap).comp i.toLinearMap = f
    rw [LinearMap.comp_assoc, hr, LinearMap.comp_id]

/-- A smooth linear map lifts through every surjective intertwiner of smooth targets. -/
theorem lift_smooth (hσ : IsSmooth σ) (q : σ.IntertwiningMap τ)
    (hq : Function.Surjective q) (f : V →ₗ[ℂ] U)
    (hf : f ∈ smoothVectors (Representation.linHom ρ τ)) :
    ∃ f' ∈ smoothVectors (Representation.linHom ρ σ), q.toLinearMap.comp f' = f := by
  obtain ⟨H, hH⟩ := hf
  obtain ⟨K, hKH, hK, -⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ H
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  let ρK : Representation ℂ K V := ρ.comp K.toSubgroup.subtype
  let σK : Representation ℂ K W := σ.comp K.toSubgroup.subtype
  let τK : Representation ℂ K U := τ.comp K.toSubgroup.subtype
  let qK : σK.IntertwiningMap τK :=
    { toLinearMap := q.toLinearMap
      isIntertwining' := fun k => q.isIntertwining' k.val }
  let fK : ρK.IntertwiningMap τK :=
    { toLinearMap := f
      isIntertwining' := by
        intro k
        ext x
        exact (hom_fixed_iff ρ τ H.toSubgroup f).mp hH ⟨k.val, hKH k.property⟩ x }
  obtain ⟨s, hs⟩ := compact_section σK τK
    (isSmooth_comp _ continuous_subtype_val hσ) qK hq
  refine ⟨(s.comp fK).toLinearMap, ⟨K, ?_⟩, ?_⟩
  · exact (hom_fixed_iff ρ σ K.toSubgroup _).mpr (fun k x => (s.comp fK).isIntertwining _ _ k x)
  · change q.toLinearMap.comp (s.toLinearMap.comp f) = f
    rw [← LinearMap.comp_assoc, hs, LinearMap.id_comp]

end HomExactness

section Preservation

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable {V : Type v} {P : Type v}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P]

/-- The lifting property in the published statement, at a fixed carrier universe. -/
def IsProjective (ρ : Representation ℂ G P) : Prop :=
  ∀ (Y Z : Type v) [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (σ : Representation ℂ G Y) (τ : Representation ℂ G Z),
    IsSmooth σ → IsSmooth τ → ∀ q : σ.IntertwiningMap τ, Function.Surjective q →
      ∀ f : ρ.IntertwiningMap τ, ∃ g : ρ.IntertwiningMap σ, q.comp g = f

/-- The extension property in the published statement, at a fixed carrier universe. -/
def IsInjective (ρ : Representation ℂ G P) : Prop :=
  ∀ (X Y : Type v) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (σ : Representation ℂ G X) (τ : Representation ℂ G Y),
    IsSmooth σ → IsSmooth τ → ∀ j : σ.IntertwiningMap τ, Function.Injective j →
      ∀ f : σ.IntertwiningMap ρ, ∃ g : τ.IntertwiningMap ρ, g.comp j = f

variable (ρ : Representation ℂ G P) (π : Representation ℂ G V)

/-- Tensoring preserves projectives by the adjunction and covariant Hom exactness. -/
theorem tensor_projective (hρ : IsSmooth ρ) (_hπ : IsSmooth π)
    (hP : IsProjective ρ) : IsProjective (Representation.tprod ρ π) := by
  intro Y Z _ _ _ _ σ τ hσ _ q hq f
  let Hq := smoothMap (postcompose π σ τ q)
  have hHq : Function.Surjective Hq := by
    intro F
    obtain ⟨F', hF', hF⟩ := lift_smooth π σ τ hσ q hq F.val F.property
    exact ⟨⟨F', hF'⟩, Subtype.ext (LinearMap.ext fun x => LinearMap.congr_fun hF x)⟩
  obtain ⟨g, hg⟩ := hP _ _ _ _ (isSmooth_smoothPart _) (isSmooth_smoothPart _)
    Hq hHq (smoothIntertwinerCurry ρ π τ hρ f)
  refine ⟨(smoothIntertwinerCurry ρ π σ hρ).symm g, ?_⟩
  ext x y
  exact congrArg (fun F => (F x).val y) hg

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- Hom into an injective object is injective, by tensor exactness and currying. -/
theorem hom_injective (_hρ : IsSmooth ρ) (hπ : IsSmooth π)
    (hI : IsInjective ρ) : IsInjective (smoothPart (Representation.linHom π ρ)) := by
  intro X Y _ _ _ _ σ τ hσ hτ j hj f
  let J := j.rTensor π
  have hJ : Function.Injective J :=
    Module.Flat.rTensor_preserves_injective_linearMap j.toLinearMap hj
  obtain ⟨g, hg⟩ := hI _ _ _ _ (tensor_smooth σ π hσ hπ) (tensor_smooth τ π hτ hπ)
    J hJ ((smoothIntertwinerCurry σ π ρ hσ).symm f)
  refine ⟨smoothIntertwinerCurry τ π ρ hτ g, ?_⟩
  ext x y
  exact congrArg (fun F => F (x ⊗ₜ y)) hg

end Preservation

section Flip

variable {R : Type*} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type a} {W : Type b} {U : Type c}
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]
variable (ρ : Representation R G V) (σ : Representation R G W) (τ : Representation R G U)

/-- Transposing an equivariant bilinear map remains equivariant. -/
def flipIntertwiner (f : ρ.IntertwiningMap (Representation.linHom σ τ)) :
    σ.IntertwiningMap (Representation.linHom ρ τ) where
  toLinearMap := f.toLinearMap.flip
  isIntertwining' := by
    intro g
    ext x y
    have h := congrArg (fun F : W →ₗ[R] U => F (σ g x))
      (f.isIntertwining _ _ g (ρ g⁻¹ y))
    simpa [Representation.linHom_apply] using h

/-- Symmetry between the two source variables of an equivariant bilinear map. -/
def intertwinerFlipEquiv : ρ.IntertwiningMap (Representation.linHom σ τ) ≃ₗ[R]
    σ.IntertwiningMap (Representation.linHom ρ τ) where
  toFun := flipIntertwiner ρ σ τ
  invFun := flipIntertwiner σ ρ τ
  left_inv := by intro f; ext x y; rfl
  right_inv := by intro f; ext x y; rfl
  map_add' := by intros; ext x y; rfl
  map_smul' := by intros; ext x y; rfl

/-- Smooth source variables can be transposed in smooth equivariant Hom. -/
def smoothIntertwinerFlip (hρ : IsSmooth ρ) (hσ : IsSmooth σ) :=
  ((smoothHomEquiv hρ (Representation.linHom σ τ)).symm.trans
    (intertwinerFlipEquiv ρ σ τ)).trans
      (smoothHomEquiv hσ (Representation.linHom ρ τ))

end Flip

section ContravariantPreservation

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable {V : Type v} {P : Type v}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P]
variable (ρ : Representation ℂ G P) (π : Representation ℂ G V)

/-- Contravariant Hom sends projectives to injectives. -/
theorem hom_projective_injective (hρ : IsSmooth ρ) (hP : IsProjective ρ) :
    IsInjective (smoothPart (Representation.linHom ρ π)) := by
  intro X Y _ _ _ _ σ τ hσ hτ j hj f
  let Hj := smoothMap (precompose σ τ π j)
  have hHj : Function.Surjective Hj := by
    intro F
    obtain ⟨F', hF', hF⟩ := extend_smooth σ τ π hτ j hj F.val F.property
    exact ⟨⟨F', hF'⟩, Subtype.ext (LinearMap.ext fun x => LinearMap.congr_fun hF x)⟩
  obtain ⟨g, hg⟩ := hP _ _ _ _ (isSmooth_smoothPart _) (isSmooth_smoothPart _)
    Hj hHj (smoothIntertwinerFlip σ ρ π hσ hρ f)
  refine ⟨(smoothIntertwinerFlip τ ρ π hτ hρ).symm g, ?_⟩
  ext x y
  exact congrArg (fun F => (F y).val x) hg

end ContravariantPreservation

end Langlands.Renard.Smooth.TensorHom

namespace Langlands.Renard.Smooth

/-- Renard III.1.15, Theorem: the full published exactness and preservation claims. -/
theorem tensorHomExactness : TensorHomExactnessStatement.{u, v} := by
  intro G _ _ _ _ _ _ V _ _ π hπ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro P _ _ ρ hρ hP
    exact TensorHom.tensor_projective ρ π hρ hπ hP
  · intro W₁ W₂ _ _ _ _ σ₁ σ₂ _ h₂ i hi f hf
    exact TensorHom.extend_smooth σ₁ σ₂ π h₂ i hi f hf
  · intro P _ _ ρ hρ hP
    exact TensorHom.hom_projective_injective ρ π hρ hP
  · intro W₂ W₃ _ _ _ _ σ₂ σ₃ h₂ _ q hq f hf
    exact TensorHom.lift_smooth π σ₂ σ₃ h₂ q hq f hf
  · intro I _ _ ρ hρ hI
    exact TensorHom.hom_injective ρ π hρ hπ hI

end Langlands.Renard.Smooth
