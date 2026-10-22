import Langlands.Group.GL.BlockModulus
import Langlands.Representation.Category.Basic
import Langlands.Representation.Jacquet.Normalized

/-!
# Normalized Jacquet modules for standard block parabolics

The Jacquet module of a representation of `GL_n` along a standard block parabolic
is the actual coinvariant quotient of its restriction to the parabolic by the
unipotent radical. The Levi acts through its section into the parabolic,
normalized by the inverse square root of a supplied full positive modulus. For
p-adic fields that modulus is the explicit block modulus.
-/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.GeneralLinear.BlockShape

universe uF uV uW uX

variable {F : Type uF} [CommRing F] {n : ℕ} (B : BlockShape n)
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

/-- The actual Jacquet module `V_N`: the coinvariants of the unipotent radical in
the restriction to the parabolic. -/
abbrev JacquetModule (ρ : Representation ℂ (GeneralLinear n F) V) :=
  Jacquet.Coinvariants (ρ.comp (B.parabolic F).subtype) (B.unipotentRadical F)

/-- The quotient map `V → V_N`. -/
abbrev jacquetMk (ρ : Representation ℂ (GeneralLinear n F) V) :
    V →ₗ[ℂ] B.JacquetModule ρ :=
  Jacquet.mk (ρ.comp (B.parabolic F).subtype) (B.unipotentRadical F)

theorem jacquetMk_surjective (ρ : Representation ℂ (GeneralLinear n F) V) :
    Function.Surjective (B.jacquetMk ρ) :=
  Jacquet.mk_surjective _ _

/-- The parabolic normalizes its unipotent radical, which is normal in it. -/
theorem top_le_normalizer_unipotentRadical :
    (⊤ : Subgroup (B.parabolic F)) ≤
      Subgroup.normalizer (B.unipotentRadical F : Set (B.parabolic F)) :=
  (Subgroup.normalizer_eq_top (B.unipotentRadical F)).ge

/-- The Levi, sent into the top subgroup of the parabolic by its actual section. -/
def leviToTop : B.Levi F →* (⊤ : Subgroup (B.parabolic F)) :=
  (Subgroup.topEquiv (G := B.parabolic F)).symm.toMonoidHom.comp (B.leviInParabolic F)

@[simp]
theorem leviToTop_val (m : B.Levi F) :
    ((B.leviToTop m : (⊤ : Subgroup (B.parabolic F))) : B.parabolic F) =
      B.leviInParabolic F m := rfl

/-- A supplied full Levi modulus, inflated to the parabolic and restricted to
its top subgroup. -/
def topModulus (δ : B.Levi F →* ℝ≥0ˣ) : (⊤ : Subgroup (B.parabolic F)) →* ℝ≥0ˣ :=
  (δ.comp (B.leviProjection F)).comp (⊤ : Subgroup (B.parabolic F)).subtype

@[simp]
theorem topModulus_leviToTop (δ : B.Levi F →* ℝ≥0ˣ) (m : B.Levi F) :
    B.topModulus δ (B.leviToTop m) = δ m := by
  simp [topModulus, leviToTop]

/-- The normalized Jacquet module for a supplied full positive modulus `δ`:
the Levi acts on `V_N` by `m ↦ δ(m)^(-1/2) [ρ(m) v]`. -/
def normalizedJacquetOf (δ : B.Levi F →* ℝ≥0ˣ)
    (ρ : Representation ℂ (GeneralLinear n F) V) :
    Representation ℂ (B.Levi F) (B.JacquetModule ρ) :=
  (Jacquet.normalizedActionOfModulus (ρ.comp (B.parabolic F).subtype)
    (B.unipotentRadical F) ⊤ B.top_le_normalizer_unipotentRadical
    (B.topModulus δ)).comp B.leviToTop

theorem normalizedJacquetOf_mk (δ : B.Levi F →* ℝ≥0ˣ)
    (ρ : Representation ℂ (GeneralLinear n F) V) (m : B.Levi F) (v : V) :
    B.normalizedJacquetOf δ ρ m (B.jacquetMk ρ v) =
      (((NNReal.sqrt (δ m : ℝ≥0) : ℝ) : ℂ))⁻¹ •
        B.jacquetMk ρ (ρ (B.leviEmbedding F m) v) := by
  change Jacquet.normalizedActionOfModulus (ρ.comp (B.parabolic F).subtype)
      (B.unipotentRadical F) ⊤ B.top_le_normalizer_unipotentRadical
      (B.topModulus δ) (B.leviToTop m) (B.jacquetMk ρ v) = _
  rw [Jacquet.normalizedActionOfModulus_mk, topModulus_leviToTop]
  rfl

/-- The Jacquet map of an actual intertwiner of representations of `GL_n`. -/
def normalizedJacquetOfMap (δ : B.Levi F →* ℝ≥0ˣ)
    {ρ : Representation ℂ (GeneralLinear n F) V}
    {τ : Representation ℂ (GeneralLinear n F) W} (f : ρ.IntertwiningMap τ) :
    (B.normalizedJacquetOf δ ρ).IntertwiningMap (B.normalizedJacquetOf δ τ) where
  toLinearMap := (Jacquet.normalizedMapOfModulus (B.unipotentRadical F) ⊤
    B.top_le_normalizer_unipotentRadical (B.topModulus δ)
    (Jacquet.restrictMap f (B.parabolic F))).toLinearMap
  isIntertwining' m := (Jacquet.normalizedMapOfModulus (B.unipotentRadical F) ⊤
    B.top_le_normalizer_unipotentRadical (B.topModulus δ)
    (Jacquet.restrictMap f (B.parabolic F))).isIntertwining' (B.leviToTop m)

@[simp]
theorem normalizedJacquetOfMap_mk (δ : B.Levi F →* ℝ≥0ˣ)
    {ρ : Representation ℂ (GeneralLinear n F) V}
    {τ : Representation ℂ (GeneralLinear n F) W} (f : ρ.IntertwiningMap τ) (v : V) :
    B.normalizedJacquetOfMap δ f (B.jacquetMk ρ v) = B.jacquetMk τ (f v) := rfl

@[simp]
theorem normalizedJacquetOfMap_id (δ : B.Levi F →* ℝ≥0ˣ)
    (ρ : Representation ℂ (GeneralLinear n F) V) :
    B.normalizedJacquetOfMap δ (Representation.IntertwiningMap.id ρ) =
      Representation.IntertwiningMap.id (B.normalizedJacquetOf δ ρ) := by
  apply Representation.IntertwiningMap.ext
  apply Representation.Coinvariants.hom_ext
  rfl

@[simp]
theorem normalizedJacquetOfMap_comp (δ : B.Levi F →* ℝ≥0ˣ)
    {ρ : Representation ℂ (GeneralLinear n F) V}
    {τ : Representation ℂ (GeneralLinear n F) W}
    {υ : Representation ℂ (GeneralLinear n F) X}
    (f : ρ.IntertwiningMap τ) (g : τ.IntertwiningMap υ) :
    B.normalizedJacquetOfMap δ (g.comp f) =
      (B.normalizedJacquetOfMap δ g).comp (B.normalizedJacquetOfMap δ f) := by
  apply Representation.IntertwiningMap.ext
  apply Representation.Coinvariants.hom_ext
  rfl

/-- The parabolic Jacquet module is linearly equivalent to the coinvariants of
the ambient matrix subgroup `B.unipotentSubgroup F` in `V`. -/
def jacquetModuleEquiv (ρ : Representation ℂ (GeneralLinear n F) V) :
    B.JacquetModule ρ ≃ₗ[ℂ] Jacquet.Coinvariants ρ (B.unipotentSubgroup F) where
  __ := Jacquet.lift (ρ.comp (B.parabolic F).subtype) (B.unipotentRadical F)
    (Jacquet.mk ρ (B.unipotentSubgroup F)) (fun u => LinearMap.ext fun v =>
      Jacquet.mk_apply_subgroup ρ (B.unipotentSubgroup F)
        ⟨((u : B.parabolic F) : GeneralLinear n F), (u : B.parabolic F), u.2, rfl⟩ v)
  invFun := Jacquet.lift ρ (B.unipotentSubgroup F) (B.jacquetMk ρ) (fun u => by
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.mp u.2
    apply LinearMap.ext
    intro v
    have h := Jacquet.mk_apply_subgroup (ρ.comp (B.parabolic F).subtype)
      (B.unipotentRadical F) ⟨w, hw⟩ v
    change B.jacquetMk ρ (ρ (u : GeneralLinear n F) v) = B.jacquetMk ρ v
    rw [← hwu]
    exact h)
  left_inv x := by
    obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ x
    rfl
  right_inv x := by
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ (B.unipotentSubgroup F) x
    rfl

@[simp]
theorem jacquetModuleEquiv_mk (ρ : Representation ℂ (GeneralLinear n F) V) (v : V) :
    B.jacquetModuleEquiv ρ (B.jacquetMk ρ v) = Jacquet.mk ρ (B.unipotentSubgroup F) v := rfl

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F]

theorem isOpen_ker_topModulus (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F))) :
    IsOpen ((B.topModulus δ).ker : Set (⊤ : Subgroup (B.parabolic F))) :=
  hδ.preimage ((B.leviProjectionContinuous F).continuous.comp continuous_subtype_val)

omit [IsTopologicalRing F] in
theorem continuous_leviToTop : Continuous (B.leviToTop (F := F)) :=
  (B.leviInParabolicContinuous F).continuous.subtype_mk _

/-- For an open-kernel modulus the normalized Jacquet module of a smooth
representation is smooth. -/
theorem isSmooth_normalizedJacquetOf (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F)))
    {ρ : Representation ℂ (GeneralLinear n F) V} (hρ : IsSmooth ρ) :
    IsSmooth (B.normalizedJacquetOf δ ρ) :=
  isSmooth_comp B.leviToTop B.continuous_leviToTop
    (Jacquet.isSmooth_normalizedActionOfModulus _ _ _ _ _
      (B.isOpen_ker_topModulus δ hδ)
      (isSmooth_comp (B.parabolic F).subtype continuous_subtype_val hρ))

/-- The normalized Jacquet module of a bundled smooth representation. -/
abbrev normalizedJacquetObjectOf (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F)))
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F)) :
    SmoothRep.{0, uF, uV} ℂ (B.Levi F) :=
  SmoothRep.of (B.normalizedJacquetOf δ A.representation)
    (B.isSmooth_normalizedJacquetOf δ hδ A.isSmooth)

/-- The normalized Jacquet functor between canonical smooth categories. -/
def normalizedJacquetFunctorOf (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F))) :
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F) ⥤
      SmoothRep.{0, uF, uV} ℂ (B.Levi F) where
  obj A := B.normalizedJacquetObjectOf δ hδ A
  map f := SmoothRep.ofHom (B.normalizedJacquetOfMap δ (SmoothRep.hom f))
  map_id A := by
    change SmoothRep.ofHom (A := B.normalizedJacquetObjectOf δ hδ A)
        (B := B.normalizedJacquetObjectOf δ hδ A)
        (B.normalizedJacquetOfMap δ (Representation.IntertwiningMap.id A.representation)) =
      SmoothRep.ofHom (Representation.IntertwiningMap.id _)
    rw [normalizedJacquetOfMap_id]
  map_comp {A A' A''} f g := by
    change SmoothRep.ofHom (A := B.normalizedJacquetObjectOf δ hδ A)
        (B := B.normalizedJacquetObjectOf δ hδ A'')
        (B.normalizedJacquetOfMap δ ((SmoothRep.hom g).comp (SmoothRep.hom f))) =
      SmoothRep.ofHom ((B.normalizedJacquetOfMap δ (SmoothRep.hom g)).comp
        (B.normalizedJacquetOfMap δ (SmoothRep.hom f)))
    rw [normalizedJacquetOfMap_comp]

end Topology

end Langlands.GeneralLinear.BlockShape

namespace Langlands.PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private theorem isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The normalized Jacquet module `r_P(ρ)` of an actual p-adic field, using the
full explicit block modulus `T.leviModulus B`. -/
def normalizedJacquet (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    Representation ℂ (B.Levi F.Carrier) (B.JacquetModule ρ) :=
  B.normalizedJacquetOf (T.leviModulus B) ρ

/-- The Levi acts by `δ_P(m)^(-1/2)` times the action of the embedded block
diagonal matrix. -/
theorem normalizedJacquet_mk (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (m : B.Levi F.Carrier) (v : V) :
    T.normalizedJacquet B ρ m (B.jacquetMk ρ v) =
      (((NNReal.sqrt (T.leviModulus B m : ℝ≥0) : ℝ) : ℂ))⁻¹ •
        B.jacquetMk ρ (ρ (B.leviEmbedding F.Carrier m) v) :=
  B.normalizedJacquetOf_mk _ ρ m v

/-- The normalizing scalar is the inverse of the induction half. -/
theorem normalizedJacquet_mk_eq_inv_halfModulus
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (m : B.Levi F.Carrier) (v : V) :
    T.normalizedJacquet B ρ m (B.jacquetMk ρ v) =
      ((T.leviHalfModulus B m)⁻¹ : ℂˣ) •
        B.jacquetMk ρ (ρ (B.leviEmbedding F.Carrier m) v) := by
  rw [normalizedJacquet_mk, Units.smul_def, Units.val_inv_eq_inv_val,
    leviHalfModulus_apply]

/-- The Jacquet map of an actual intertwiner. -/
def normalizedJacquetMap {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {τ : Representation ℂ (GeneralLinear n F.Carrier) W} (f : ρ.IntertwiningMap τ) :
    (T.normalizedJacquet B ρ).IntertwiningMap (T.normalizedJacquet B τ) :=
  B.normalizedJacquetOfMap (T.leviModulus B) f

theorem isSmooth_normalizedJacquet
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V} :
    letI := T.topology
    IsSmooth ρ → IsSmooth (T.normalizedJacquet B ρ) := by
  let := T.topology
  let := T.isTopologicalRing
  exact B.isSmooth_normalizedJacquetOf (T.leviModulus B) (T.isOpen_ker_leviModulus B)

/-- The normalized Jacquet functor of canonical smooth categories. -/
def normalizedJacquetFunctor :
    letI := T.generalLinearTopology n
    letI := T.leviTopology B
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedJacquetFunctorOf (T.leviModulus B) (T.isOpen_ker_leviModulus B)

end Langlands.PadicField.TopologicalData

namespace Langlands.PadicField

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The normalized Jacquet module for the canonical realization of every
algebraic p-adic field. -/
abbrev canonicalNormalizedJacquet (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :=
  F.canonicalTopologicalData.normalizedJacquet B ρ

/-- The canonical normalized Jacquet functor. -/
abbrev canonicalNormalizedJacquetFunctor :
    letI := F.canonicalGeneralLinearTopology n
    letI := F.canonicalLeviTopology B
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) :=
  F.canonicalTopologicalData.normalizedJacquetFunctor B

end Langlands.PadicField
