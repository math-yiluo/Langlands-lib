import Langlands.GroupScheme.Rational.CrossTorusLieTransport
import Langlands.GroupScheme.Rational.SplitTorusFiniteRank
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacterProof
import Langlands.GroupScheme.Lie.SelfCentralizing

/-! # Actual Lie coordinates and dimensions of split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace splitTorus

variable {R : CommRingCat.{u}} (I : Type u) [Finite I]
  (A : Type u) [CommRing A] [Algebra R A]

local instance : IsAffineHom (splitTorus (Spec R) I).X.hom :=
  isAffineHom_splitTorus_spec R I

/-- Every tangent point of a split torus has independent infinitesimal unit coordinates. -/
theorem infinitesimalLinear_surjective :
    Function.Surjective (infinitesimalLinear (R := R) I A) := by
  intro x
  let t := algebraPointsEquiv I (DualNumber A) x.toMul.val
  have hfst (i : I) : (t i).val.fst = 1 := by
    have h := congrArg (fun y => (algebraPointsEquiv I A y i : A)) x.toMul.property
    rw [Lie.reduction, algebraPointsEquiv_naturality] at h
    simpa [t] using h
  refine ⟨fun i => (t i).val.snd, ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  apply (algebraPointsEquiv I (DualNumber A)).injective
  change algebraPointsEquiv I (DualNumber A)
      ((algebraPointsEquiv I (DualNumber A)).symm _) = t
  rw [MulEquiv.apply_symm_apply]
  funext i
  apply Units.ext
  ext
  · exact (hfst i).symm
  · rfl

/-- Independent infinitesimal coordinates give the actual Lie kernel of a split torus. -/
def infinitesimalLinearEquiv :
    (I → A) ≃ₗ[A] Additive (lieKernel (splitTorus (Spec R) I) A) :=
  LinearEquiv.ofBijective (infinitesimalLinear (R := R) I A)
    ⟨infinitesimalLinear_injective I A, infinitesimalLinear_surjective I A⟩

@[simp] theorem infinitesimalLinearEquiv_apply (v : I → A) :
    infinitesimalLinearEquiv (R := R) I A v = infinitesimalLinear I A v := rfl

/-- The actual Lie dimension of a split torus equals the number of its factors. -/
theorem finrank_lieKernel (k : Type u) [Field k] :
    Module.finrank k (Additive (lieKernel
      (splitTorus (Spec (CommRingCat.of k)) I) k)) = Nat.card I := by
  let := Fintype.ofFinite I
  simpa only [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using
    (infinitesimalLinearEquiv (R := CommRingCat.of k) I k).finrank_eq.symm

end splitTorus

variable {k : Type u} [Field k]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom T.toGrp.X.hom] [IsAffineHom T'.toGrp.X.hom]

/-- For a split torus, actual Lie dimension equals the integral cocharacter rank. -/
theorem IsSplitTorus.finrank_lieKernel_eq_cocharacter (hT : IsSplitTorus T.toGrp) :
    Module.finrank k (Additive (lieKernel T.toGrp k)) =
      Module.finrank ℤ (cocharacterLattice T) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := hI
  let := Fintype.ofFinite I
  let : IsAffineHom (splitTorus (Spec (CommRingCat.of k)) I).X.hom :=
    isAffineHom_splitTorus_spec _ I
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    CommGroupScheme.isoOfGroupIso e
  let eZ : cocharacterLattice T ≃ₗ[ℤ] (I → ℤ) := ((cocharacterLattice.congr eC).trans
    (splitTorus.cocharacterLatticeEquiv k I)).toIntLinearEquiv
  calc
    Module.finrank k (Additive (lieKernel T.toGrp k)) =
        Module.finrank k (Additive (lieKernel
          (splitTorus (Spec (CommRingCat.of k)) I) k)) :=
      (Lie.targetEquiv e k).finrank_eq
    _ = Nat.card I := splitTorus.finrank_lieKernel I k
    _ = Module.finrank ℤ (cocharacterLattice T) := by
      simpa only [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using
        eZ.finrank_eq.symm

/-- Isogenies of split tori preserve actual Lie dimensions in every characteristic. -/
theorem IsSplitTorus.finrank_lieKernel_eq_of_isogeny
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp) (f : T ⟶ T')
    (hf : IsIsogeny (CommGroupScheme.groupHom f)) :
    Module.finrank k (Additive (lieKernel T.toGrp k)) =
      Module.finrank k (Additive (lieKernel T'.toGrp k)) := by
  have := hT.finite_cocharacterLattice
  have := hT'.finite_cocharacterLattice
  obtain ⟨n, hn, g, hfg, hgf⟩ := hT.exists_isogeny_quasiInverse hT' f hf
  have hf' := (SplitTorusIsogeny.cocharacter_isogeny_conclusions_of_quasiInverse
    f g n hn hT hT' hfg hgf).1
  have hg' := (SplitTorusIsogeny.cocharacter_isogeny_conclusions_of_quasiInverse
    g f n hn hT' hT hgf hfg).1
  rw [hT.finrank_lieKernel_eq_cocharacter, hT'.finrank_lieKernel_eq_cocharacter]
  exact le_antisymm (LinearMap.finrank_le_finrank_of_injective hf')
    (LinearMap.finrank_le_finrank_of_injective hg')

namespace Lie

/-- Self-centralizing split tori linked by an isogeny have equally dimensional zero weights. -/
theorem finrank_zeroWeight_eq_of_torus_isogeny
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom]
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G')
    [Mono i.hom.hom] [Mono i'.hom.hom]
    (hself : torusCentralizer i = SubgroupFunctor.range i)
    (hself' : torusCentralizer i' = SubgroupFunctor.range i')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (f : T ⟶ T') (hf : IsIsogeny (CommGroupScheme.groupHom f)) :
    Module.finrank k (weightSpace i 0) = Module.finrank k (weightSpace i' 0) := by
  rw [finrank_zeroWeight_of_selfCentralizing i hself,
    finrank_zeroWeight_of_selfCentralizing i' hself']
  exact hT.finrank_lieKernel_eq_of_isogeny hT' f hf

end Lie

end Langlands.GroupScheme
