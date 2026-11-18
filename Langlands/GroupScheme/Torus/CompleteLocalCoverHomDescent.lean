import Langlands.GroupScheme.Torus.CompleteLocalDeformation.CoverDescent

/-! # Descent equivalence for homomorphisms with a prescribed special fibre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.CompleteLocalDeformation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  {G H : GroupScheme (Spec (CommRingCat.of A))} [IsAffineHom G.X.hom]

/-- Actual homomorphisms with a prescribed special fibre are equivalent to
homomorphisms over the local splitting cover with the transported special fibre.
No completeness or target flatness hypothesis is needed. -/
def specialHomCoverEquiv (d : LocalSplittingData A H)
    (hG : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange
        (Spec.algebraMap d.Carrier (IsLocalRing.ResidueField d.Carrier))).obj
          ((GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).obj G)))
    (f₀ : (GroupScheme.baseChange
        (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj H ⟶
      (GroupScheme.baseChange
        (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G) :
    {f : H ⟶ G //
      (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map f = f₀} ≃
    {fB : (GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).obj H ⟶
        (GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).obj G //
      (GroupScheme.baseChange
        (Spec.algebraMap d.Carrier (IsLocalRing.ResidueField d.Carrier))).map fB =
          specialHomTransport (B := d.Carrier) f₀} :=
  Equiv.ofBijective
    (fun f => ⟨(GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).map f.val, by
      rw [← specialHomTransport_baseChange (B := d.Carrier) f.val, f.property]⟩)
    (by
      constructor
      · intro f g hfg
        apply Subtype.ext
        apply (GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).map_injective
        exact congrArg Subtype.val hfg
      · intro fB
        obtain ⟨f, hfB, hf⟩ := exists_descent_of_specialHomTransport
          d hG f₀ fB.val fB.property
        exact ⟨⟨f, hf⟩, Subtype.ext hfB⟩)

/-- The forward descent equivalence is actual base change. -/
@[simp] theorem specialHomCoverEquiv_apply_val (d : LocalSplittingData A H)
    (hG : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange
        (Spec.algebraMap d.Carrier (IsLocalRing.ResidueField d.Carrier))).obj
          ((GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).obj G)))
    (f₀ : (GroupScheme.baseChange
        (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj H ⟶
      (GroupScheme.baseChange
        (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G)
    (f : {f : H ⟶ G //
      (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map f = f₀}) :
    (specialHomCoverEquiv d hG f₀ f).val =
      (GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).map f.val := rfl

end Langlands.GroupScheme.CompleteLocalDeformation
