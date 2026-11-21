import Langlands.TraceFormula.CyclicDiscreteWeylWeights
import Langlands.GroupScheme.Dynamic.GeneralLinearDecomposition
import Langlands.GroupScheme.Reductive.GeneralLinearWeyl

/-! # Presentations of the coordinate Levi subgroups in the discrete trace sum -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.TraceFormula.CoordinateLevi

open Langlands.GeneralLinear (BlockShape)
open Langlands.GroupScheme.GeneralLinear

variable {n : ℕ} (L : CoordinateLevi n)

/-- A presentation of a coordinate partition by ordered consecutive blocks and a permutation
carrying those blocks onto the specified coordinate sets. -/
structure Presentation where
  shape : BlockShape n
  blocks : Fin shape.length ≃ L.Block
  coordinates : Equiv.Perm (Fin n)
  block_image (i : Fin shape.length) :
    Set.range (fun j => coordinates (shape.index i j)) = (blocks i).val

namespace Presentation

variable {L} (P : L.Presentation)

/-- The weight of an actual coordinate is minus the index of its block in the presentation. -/
def weight (i : Fin n) : ℤ := blockShapeWeight P.shape (P.coordinates.symm i)

/-- Regular Weyl elements preserve block sizes and are regular modulo the ambient split centre. -/
abbrev RegularWeyl (L : CoordinateLevi n) := {s // s ∈ L.regularWeyl}

/-- The rational permutation representative sends the `j`th coordinate of a block to the
`j`th coordinate of its image in the chosen presentation. -/
def weylPermutation (s : RegularWeyl L) : Equiv.Perm (Fin n) := by
  classical
  let p := P.blocks.trans (s.val.trans P.blocks.symm)
  have hsize (i : Fin P.shape.length) : P.shape.size i = P.shape.size (p i) := by
    have card (k : Fin P.shape.length) : P.shape.size k = (P.blocks k).val.card := by
      let e : Fin (P.shape.size k) ≃ (P.blocks k).val := Equiv.ofBijective
        (fun j => ⟨P.coordinates (P.shape.index k j), by
          change P.coordinates (P.shape.index k j) ∈ ((P.blocks k).val : Set (Fin n))
          rw [← P.block_image k]
          exact Set.mem_range_self j⟩) (by
            constructor
            · intro a b h
              exact (P.shape.index k).injective (P.coordinates.injective (congrArg Subtype.val h))
            · intro j
              have hj : j.val ∈ Set.range (fun i => P.coordinates (P.shape.index k i)) := by
                rw [P.block_image k]
                exact j.property
              obtain ⟨i, hi⟩ := hj
              exact ⟨i, Subtype.ext hi⟩)
      simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_congr e
    rw [card i, card (p i)]
    have hs := ((Finset.mem_filter.mp s.property).2.1) (P.blocks i)
    simpa [p] using hs.symm
  let e := P.shape.indexEquiv.trans P.coordinates
  exact e.symm.trans ((Equiv.sigmaCongr p (fun i => finCongr (hsize i))).trans e)

/-- The actual block parabolic in the ambient coordinates. -/
abbrev parabolic (K : Type u) [Field K] := blockParabolicScheme (Fin n) (CommRingCat.of K) P.weight

/-- The actual block Levi in the ambient coordinates. -/
abbrev levi (K : Type u) [Field K] := blockLeviScheme (Fin n) (CommRingCat.of K) P.weight

/-- The actual unipotent radical in the ambient coordinates. -/
abbrev unipotent (K : Type u) [Field K] := blockUnipotentScheme (Fin n) (CommRingCat.of K) P.weight

end Presentation

/-- A coordinate Levi admits an ordered block presentation. In such a presentation the three
coordinate subgroups are the conjugates of the actual standard block subgroups. -/
def CoordinateLeviPresentationStatement : Prop :=
  ∀ (n : ℕ) (L : CoordinateLevi n), Nonempty L.Presentation ∧
    ∀ (P : L.Presentation) (R : Type u) [CommRing R],
      let c := (MulAut.conj (permGL R P.coordinates)).toMonoidHom
      (P.shape.parabolic R).map c = blockParabolicSubgroup R P.weight ∧
      (P.shape.leviSubgroup R).map c = blockLeviSubgroup R P.weight ∧
      (P.shape.unipotentSubgroup R).map c = blockUnipotentSubgroup R P.weight ∧
      ∀ (s : Presentation.RegularWeyl L) (b : L.Block),
        Set.image (P.weylPermutation s) b.val = (s.val b).val

end Langlands.TraceFormula.CoordinateLevi
