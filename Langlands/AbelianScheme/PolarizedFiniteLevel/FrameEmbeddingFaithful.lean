import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingTransport
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicBundlePolarizationDeterminationStatement
import Langlands.AbelianScheme.PointedMorphismRigidityProof
import Langlands.AlgebraicGeometry.Picard.LineBundleInverse

/-! # A frame-normalized datum is determined by its embedded image and torsion points -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard GroupScheme.Tate

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n m : ℕ}

/-- The torsion point with zero coefficients is the unit section. -/
lemma Datum.torsionPoint_zero (a : Datum P S g d n) :
    a.torsionPoint 0 = (CartesianMonoidalCategory.toUnit (Over.mk (𝟙 S)) ≫
      η[a.abelian.X]).left := by
  simp only [Datum.torsionPoint, map_zero]
  rfl

/-- The `i`-th level section is the torsion point with the `i`-th unit coefficient tuple. -/
lemma Datum.torsionPoint_single (a : Datum P S g d n) (i : Fin (2 * g)) :
    a.torsionPoint (Pi.single i 1) = (Additive.toMul (a.level.sections i)).val.left := by
  simp only [Datum.torsionPoint, enumerateTuple_single]

/-- Two data over a locally noetherian base with frame-normalized cubic embeddings realizing
the same embedded family are polarized-isomorphic. -/
theorem Datum.nonempty_polarizedIso_of_realizes
    (HP : CubicBundlePolarizationDeterminationStatement.{u}) [IsLocallyNoetherian S]
    {a b : Datum P S g d n} {ρ : Fin (m + 2) → Fin (2 * g) → ZMod n}
    {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m}
    {ψ' : b.abelian.X.left ⟶ RelativeProjectiveSpace S m}
    {I : (RelativeProjectiveSpace S m).IdealSheafData}
    {σ : (Fin (2 * g) → ZMod n) → (S ⟶ ProjectiveSpace (ULift.{u} ℤ) m)}
    (h : a.IsFrameEmbedding ρ ψ) (h' : b.IsFrameEmbedding ρ ψ')
    (hr : a.Realizes ψ I σ) (hr' : b.Realizes ψ' I σ) :
    Nonempty (PolarizedIso a b) := by
  have := h.isClosedImmersion
  have := h'.isClosedImmersion
  have hker : ψ'.ker = ψ.ker := hr'.1.trans hr.1.symm
  let φ := IsClosedImmersion.lift ψ' ψ hker.le
  have hφ : φ ≫ ψ' = ψ := IsClosedImmersion.lift_fac _ _ _
  have : IsIso φ := IsClosedImmersion.isIso_lift ψ' ψ hker
  have hφπ : φ ≫ b.abelian.X.hom = a.abelian.X.hom := by
    rw [← h'.toBase, ← h.toBase, ← hφ, Category.assoc]
  have hpt : ∀ r, a.torsionPoint r ≫ φ = b.torsionPoint r := by
    intro r
    rw [← cancel_mono ψ', Category.assoc, hφ]
    apply RelativeProjectiveSpace.hom_ext
    · rw [Category.assoc, Category.assoc, h.toBase, h'.toBase, Datum.torsionPoint_hom,
        Datum.torsionPoint_hom]
    · rw [Category.assoc, Category.assoc, hr.2 r, hr'.2 r]
  -- the isomorphism of schemes over the base
  let eO : a.abelian.X ≅ b.abelian.X := Over.isoMk (asIso φ) hφπ
  have hunit : η[a.abelian.X] ≫ eO.hom = η[b.abelian.X] := by
    have h0 := hpt 0
    rw [a.torsionPoint_zero, b.torsionPoint_zero] at h0
    have hiso : IsIso (CartesianMonoidalCategory.toUnit (Over.mk (𝟙 S))).left := by
      have : IsIso (CartesianMonoidalCategory.toUnit (Over.mk (𝟙 S))) :=
        Limits.isIso_of_isTerminal Over.mkIdTerminal
          CartesianMonoidalCategory.isTerminalTensorUnit _
      infer_instance
    apply Over.OverMorphism.ext
    rw [← cancel_epi (CartesianMonoidalCategory.toUnit (Over.mk (𝟙 S))).left]
    simp only [Over.comp_left] at h0 ⊢
    rw [Category.assoc] at h0
    exact h0
  have hmon : IsMonHom eO.hom :=
    Langlands.AbelianScheme.pointedMorphismRigidity S a.abelian.toGrp b.abelian.toGrp
      ⟨inferInstance, inferInstance, inferInstance⟩ inferInstance inferInstance inferInstance
      eO.hom hunit
  let gIso : a.abelian.toGrp ≅ b.abelian.toGrp :=
    { hom := Grp.homMk eO.hom
      inv := Grp.homMk eO.inv
      hom_inv_id := by
        apply Grp.hom_ext
        exact eO.hom_inv_id
      inv_hom_id := by
        apply Grp.hom_ext
        exact eO.inv_hom_id }
  let e : a.abelian ≅ b.abelian :=
    { hom := Additive.ofMul gIso.hom
      inv := Additive.ofMul gIso.inv
      hom_inv_id := congrArg Additive.ofMul gIso.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul gIso.inv_hom_id }
  have he : hom e.hom = φ := rfl
  -- the polarization
  obtain ⟨N, ⟨i⟩⟩ := h.cubic
  obtain ⟨N', ⟨i'⟩⟩ := h'.cubic
  have hcls : ((LineBundle.pullback (hom e.hom)).obj b.cubicBundle).classOf =
      (LineBundle.tensor P.preservation a.cubicBundle
        ((LineBundle.pullback a.abelian.X.hom).obj
          (LineBundle.tensor P.preservation N N'.inverse))).classOf := by
    have h1 : ((LineBundle.pullback ψ).obj (RelativeProjectiveSpace.twistOne S m)).classOf =
        ((LineBundle.pullback φ).obj ((LineBundle.pullback ψ').obj
          (RelativeProjectiveSpace.twistOne S m))).classOf := by
      rw [LineBundle.classOf_eq_iff_iso]
      exact ⟨eqToIso (congrArg (fun f => (LineBundle.pullback f).obj
        (RelativeProjectiveSpace.twistOne S m)) hφ.symm) ≪≫
        ((LineBundle.pullbackComp _ _).app _).symm⟩
    have h2 : ((LineBundle.pullback φ).obj ((LineBundle.pullback b.abelian.X.hom).obj N')).classOf
        = ((LineBundle.pullback a.abelian.X.hom).obj N').classOf := by
      rw [LineBundle.classOf_eq_iff_iso]
      exact ⟨(LineBundle.pullbackComp _ _).app _ ≪≫
        eqToIso (congrArg (fun f => (LineBundle.pullback f).obj N') hφπ)⟩
    rw [(LineBundle.classOf_eq_iff_iso _ _).mpr ⟨i⟩, (LineBundle.classOf_eq_iff_iso _ _).mpr
      ⟨(LineBundle.pullback φ).mapIso i'⟩] at h1
    rw [LineBundle.classOf_tensor P.preservation,
      ← Group.pullback_lineBundle_classOf φ, LineBundle.classOf_tensor P.preservation, map_add,
      Group.pullback_lineBundle_classOf φ b.cubicBundle, Group.pullback_lineBundle_classOf φ,
      h2] at h1
    rw [he, LineBundle.classOf_tensor P.preservation,
      ← Group.pullback_lineBundle_classOf a.abelian.X.hom
        (LineBundle.tensor P.preservation N N'.inverse),
      LineBundle.classOf_tensor P.preservation, LineBundle.classOf_inverse, map_add, map_neg,
      Group.pullback_lineBundle_classOf a.abelian.X.hom N,
      Group.pullback_lineBundle_classOf a.abelian.X.hom N', ← add_assoc, h1]
    abel
  have hpol := HP P S g d n a b e _ ((LineBundle.classOf_eq_iff_iso _ _).mp hcls)
  refine ⟨{ abelianIso := e, polarization_eq := hpol, level_eq := fun j => ?_ }⟩
  apply toSection_injective b.abelian.toGrp (Over.mk (𝟙 S)) n
  change Additive.ofMul ((Additive.toMul (a.level.sections j)).val ≫
      (groupHom e.hom).hom.hom) = Additive.ofMul (Additive.toMul (b.level.sections j)).val
  congr 1
  apply Over.OverMorphism.ext
  rw [Over.comp_left, ← a.torsionPoint_single, ← b.torsionPoint_single]
  exact hpt _

end Langlands.AbelianScheme.PolarizedFiniteLevel
