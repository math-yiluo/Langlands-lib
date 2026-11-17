import Langlands.GroupScheme.Torus.MultiplicativeTypeFpqcTransfer
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.LocallyConstant.Basic

/-! # Geometric fibre conditions and torsion orders under fpqc base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.FpqcMultiplicativeType

variable {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)

/-- The field-level multiplicative-type property of a geometric fibre is
unchanged after extending the base at a point above it. -/
theorem geometricFiber_isMultiplicativeType_iff (t : T) :
    IsMultiplicativeType (geometricFiber ((baseChange b).obj G) t) ↔
      IsMultiplicativeType (geometricFiber G (b t)) := by
  let := RelativeLevi.residueFieldAlgebra b t
  let : Algebra (AlgebraicClosure (S.residueField (b t)))
      (AlgebraicClosure (T.residueField t)) :=
    (algebraicClosureEmbedding (S.residueField (b t)) (T.residueField t)).toRingHom.toAlgebra
  let e := (RelativeLevi.geometricFiberBaseChangeIso b t).app G
  constructor
  · intro h
    exact IsMultiplicativeType.of_fieldExtension (h.of_iso e)
  · intro h
    exact h.fieldExtension.of_iso e.symm

/-- Surjective base change detects multiplicative type in every geometric fibre. -/
theorem forall_geometricFiber_isMultiplicativeType_iff [Surjective b] :
    (∀ t : T, IsMultiplicativeType (geometricFiber ((baseChange b).obj G) t)) ↔
      ∀ s : S, IsMultiplicativeType (geometricFiber G s) := by
  constructor
  · intro h s
    obtain ⟨t, rfl⟩ := b.surjective s
    exact (geometricFiber_isMultiplicativeType_iff b G t).mp (h t)
  · intro h t
    exact (geometricFiber_isMultiplicativeType_iff b G t).mpr (h (b t))

/-- Restriction of a group-scheme isomorphism to its actual integer torsion. -/
def torsionIso {U V : GroupScheme S} [IsCommMonObj U.X] [IsCommMonObj V.X]
    (e : U ≅ V) (n : ℤ) : torsion U n ≅ torsion V n where
  hom := torsionMap e.hom n
  inv := torsionMap e.inv n
  hom_inv_id := by rw [← torsionMap_comp, e.hom_inv_id, torsionMap_id]
  inv_hom_id := by rw [← torsionMap_comp, e.inv_hom_id, torsionMap_id]

/-- The coordinate dimension of the integer-torsion scheme in the chosen
geometric fibre. -/
def geometricTorsionOrder [IsCommMonObj G.X] (n : ℤ) (s : S) : ℕ :=
  coordinateOrder (torsion (geometricFiber G s) n).X

/-- Geometric torsion orders of an affine commutative group are unchanged by
arbitrary base change at every point upstairs. -/
theorem geometricTorsionOrder_baseChange [IsCommMonObj G.X] [IsAffineHom G.X.hom]
    (n : ℤ) (t : T) :
    geometricTorsionOrder ((baseChange b).obj G) n t =
      geometricTorsionOrder G n (b t) := by
  let := RelativeLevi.residueFieldAlgebra b t
  let : Algebra (AlgebraicClosure (S.residueField (b t)))
      (AlgebraicClosure (T.residueField t)) :=
    (algebraicClosureEmbedding (S.residueField (b t)) (T.residueField t)).toRingHom.toAlgebra
  let H := geometricFiber G (b t)
  have : IsAffineHom H.X.hom := by
    change IsAffineHom (pullback.snd _ _)
    infer_instance
  have : IsAffineHom (torsion H n).X.hom := by
    rw [← Over.w (torsionι H n).hom.hom]
    infer_instance
  have : IsAffine (torsion H n).X.left :=
    isAffine_of_isAffineHom (torsion H n).X.hom
  let e₀ : (baseChange (RelativeLevi.geometricPointMap b t)).obj H ≅
      geometricFiber ((baseChange b).obj G) t :=
    (RelativeLevi.geometricFiberBaseChangeIso b t).app G
  let e := torsionBaseChangeIso (RelativeLevi.geometricPointMap b t) H n ≪≫
    torsionIso e₀ n
  exact (coordinateOrder_iso ((Grp.forget _).mapIso e)).symm.trans
    (coordinateOrder_baseChange (torsion H n).X)

/-- A function on the base is locally constant exactly when its pullback along
an fpqc morphism is locally constant. -/
theorem isLocallyConstant_comp_iff [Flat b] [Surjective b] [QuasiCompact b]
    {A : Type*} (f : S → A) :
    IsLocallyConstant (f ∘ b) ↔ IsLocallyConstant f := by
  constructor
  · intro h
    apply IsLocallyConstant.iff_isOpen_fiber.mpr
    intro a
    exact (Flat.isQuotientMap_of_surjective b).isOpen_preimage.mp (h.isOpen_fiber a)
  · intro h
    exact h.comp_continuous b.continuous

/-- Local constancy of every specified torsion-order function is reflected by
fpqc base change. -/
theorem isLocallyConstant_geometricTorsionOrder_iff [IsCommMonObj G.X]
    [IsAffineHom G.X.hom] [Flat b] [Surjective b] [QuasiCompact b] (n : ℤ) :
    IsLocallyConstant (geometricTorsionOrder ((baseChange b).obj G) n) ↔
      IsLocallyConstant (geometricTorsionOrder G n) := by
  have heq : geometricTorsionOrder ((baseChange b).obj G) n =
      geometricTorsionOrder G n ∘ b :=
    funext (geometricTorsionOrder_baseChange b G n)
  rw [heq]
  exact isLocallyConstant_comp_iff b _

end Langlands.GroupScheme.FpqcMultiplicativeType
