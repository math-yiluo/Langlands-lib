import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalExtension

/-! # Finite affinoid tests for pairs of maps into a complete algebra -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open GeneralizedTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {B C : PresentedAffinoidAlgebra K}
  {L : Type v} [NormedCommRing L] [NormedAlgebra K L]

/-- Two bounded maps factor through one finite presented affinoid, which
embeds algebraically into their common target. No inverse norm bound is claimed. -/
structure FiniteJointImage (f : BoundedAlgHom K B L) (g : BoundedAlgHom K C L) where
  algebra : PresentedAffinoidAlgebra K
  left : BoundedAlgHom K B algebra
  right : BoundedAlgHom K C algebra
  embed : BoundedAlgHom K algebra L
  injective_embed : Function.Injective embed
  embed_left : embed.comp left = f
  embed_right : embed.comp right = g

variable [IsUltrametricDist L] [CompleteSpace L]

/-- Evaluate both coordinate blocks and divide by the closed kernel. -/
def finiteJointImage (f : BoundedAlgHom K B L) (g : BoundedAlgHom K C L) :
    FiniteJointImage f g := by
  let r := B.polyradius.append C.polyradius
  let b := Fin.append (fun i => f (coordinate K B i)) (fun j => g (coordinate K C j))
  have hb : HasBoundedMonomials r L b :=
    hasBoundedMonomials_append B.polyradius C.polyradius L _ _
      (hasBoundedMonomials_coordinate K L B f)
      (hasBoundedMonomials_coordinate K L C g)
  let q := evaluateHom r K L b hb
  have hl : q.comp (appendLeft B.polyradius C.polyradius K) =
      f.comp (presentationMap K B) := by
    apply GeneralizedTateAlgebra.hom_ext B.polyradius K L
    intro i
    change q (appendLeft B.polyradius C.polyradius K (X B.polyradius K i)) =
      f (coordinate K B i)
    rw [appendLeft_X]
    exact (evaluate_X r K L b (Fin.castAdd C.arity i)).trans (Fin.append_left _ _ i)
  have hr : q.comp (appendRight B.polyradius C.polyradius K) =
      g.comp (presentationMap K C) := by
    apply GeneralizedTateAlgebra.hom_ext C.polyradius K L
    intro i
    change q (appendRight B.polyradius C.polyradius K (X C.polyradius K i)) =
      g (coordinate K C i)
    rw [appendRight_X]
    exact (evaluate_X r K L b (Fin.natAdd B.arity i)).trans (Fin.append_right _ _ i)
  let D : PresentedAffinoidAlgebra K :=
    { arity := B.arity + C.arity
      polyradius := r
      ideal := RingHom.ker q.toAlgHom.toRingHom
      ideal_closed := isClosed_eq q.continuous continuous_const }
  letI := D.ideal_closed
  let e : BoundedAlgHom K D L :=
    BoundedAlgHom.liftQuotient K D.ideal q (fun _ h => h)
  have he : Function.Injective e := by
    change Function.Injective (Ideal.kerLiftAlg q.toAlgHom)
    exact Ideal.kerLiftAlg_injective _
  let l₀ := (presentationMap K D).comp (appendLeft B.polyradius C.polyradius K)
  let r₀ := (presentationMap K D).comp (appendRight B.polyradius C.polyradius K)
  have hli : ∀ a ∈ B.ideal, l₀ a = 0 := by
    intro a ha
    apply (presentationMap_eq_zero_iff K D _).mpr
    change q (appendLeft B.polyradius C.polyradius K a) = 0
    calc
      _ = f (presentationMap K B a) :=
        congrArg (fun η : BoundedAlgHom K (GeneralizedTateAlgebra B.polyradius K) L =>
          η a) hl
      _ = 0 := by rw [(presentationMap_eq_zero_iff K B a).mpr ha, map_zero]
  have hri : ∀ a ∈ C.ideal, r₀ a = 0 := by
    intro a ha
    apply (presentationMap_eq_zero_iff K D _).mpr
    change q (appendRight B.polyradius C.polyradius K a) = 0
    calc
      _ = g (presentationMap K C a) :=
        congrArg (fun η : BoundedAlgHom K (GeneralizedTateAlgebra C.polyradius K) L =>
          η a) hr
      _ = 0 := by rw [(presentationMap_eq_zero_iff K C a).mpr ha, map_zero]
  letI := B.ideal_closed
  letI := C.ideal_closed
  let l : BoundedAlgHom K B D := BoundedAlgHom.liftQuotient K B.ideal l₀ hli
  let r' : BoundedAlgHom K C D := BoundedAlgHom.liftQuotient K C.ideal r₀ hri
  refine ⟨D, l, r', e, he, ?_, ?_⟩
  · apply hom_ext_presentation K L B
    intro a
    change q (appendLeft B.polyradius C.polyradius K a) = f (presentationMap K B a)
    exact congrArg
      (fun η : BoundedAlgHom K (GeneralizedTateAlgebra B.polyradius K) L => η a) hl
  · apply hom_ext_presentation K L C
    intro a
    change q (appendRight B.polyradius C.polyradius K a) = g (presentationMap K C a)
    exact congrArg
      (fun η : BoundedAlgHom K (GeneralizedTateAlgebra C.polyradius K) L => η a) hr

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- A commuting equation in the target already holds in the joint test algebra. -/
theorem FiniteJointImage.comp_eq {f : BoundedAlgHom K B L} {g : BoundedAlgHom K C L}
    (D : FiniteJointImage f g) {A : PresentedAffinoidAlgebra K}
    (i : BoundedAlgHom K A B) (j : BoundedAlgHom K A C)
    (h : f.comp i = g.comp j) : D.left.comp i = D.right.comp j := by
  apply BoundedAlgHom.ext
  intro a
  apply D.injective_embed
  calc
    D.embed (D.left (i a)) = f (i a) :=
      congrArg (fun η : BoundedAlgHom K B L => η (i a)) D.embed_left
    _ = g (j a) := congrArg (fun η : BoundedAlgHom K A L => η a) h
    _ = D.embed (D.right (j a)) :=
      (congrArg (fun η : BoundedAlgHom K C L => η (j a)) D.embed_right).symm

end Langlands.Analytic.PresentedAffinoidAlgebra
