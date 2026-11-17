import Langlands.GroupScheme.Reductive.GlobalRootDatumComparison
import Langlands.GroupScheme.Reductive.ConnectedBasedBorel
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.GroupScheme.Rational.CocenterCoweightDescent

/-! # Full based coordinate root-data comparison over a connected base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace CoordinateRootDatum

open StarActionIndependence

/-- Realization as the full datum of a closed split torus forces finiteness
of the Weyl group on the entire coordinate lattice. -/
theorem finite_weylGroup_of_realized
    {I J : Type u} [Fintype I] (P : RootDatum J (I → ℤ) (I → ℤ))
    (k : Type u) [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    (t : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)
    (ht : IsClosedSubgroup t)
    (hP : letI := hG.isAffineHom; IsRootDatumOf t (fieldRealization k P)) :
    Finite P.weylGroup := by
  let := hG.isAffineHom
  let := hG.smooth
  let : IsClosedImmersion t.hom.hom.left := ht
  let : Finite (weylImage (T := splitTorus.commGroupScheme _ I) t) :=
    finite_weylImage_standard G I t ht
  let : Finite (fieldRealization k P).weylGroup := hP.finite_abstractWeylGroup
  let e := fieldRealizationEquiv k P
  let f : P.weylGroup → (fieldRealization k P).weylGroup := fun w =>
    ⟨conjAut e w.val, conjAut_mem_weylGroup e w.property⟩
  apply Finite.of_injective f
  intro a b hab
  apply Subtype.ext
  apply equiv_ext_of_weightMap
  intro x
  apply e.weightEquiv.injective
  have h := congrArg (fun z : (fieldRealization k P).Aut =>
    z.weightMap (e.weightEquiv x)) (congrArg Subtype.val hab)
  change (conjAut e a.val).weightMap (e.weightEquiv x) =
    (conjAut e b.val).weightMap (e.weightEquiv x) at h
  simp only [conjAut_weightMap, LinearEquiv.symm_apply_apply] at h
  simpa only [RootPairing.Equiv.weightEquiv_apply] using h

/-- The same full Weyl finiteness follows from any global coordinate datum
over a nonempty base, by realization on one residue fibre. -/
theorem finite_weylGroup_of_global
    {S : Scheme.{u}} [Nonempty S] {I J : Type u} [Fintype I]
    {G : GroupScheme S} (hG : IsReductive G)
    (t : splitTorus S I ⟶ G) (ht : IsClosedSubgroup t)
    (P : RootDatum J (I → ℤ) (I → ℤ))
    (hP : letI := hG.isAffineHom; IsGlobalCoordinateRootDatumOf I G t P) :
    Finite P.weylGroup := by
  let := hG.isAffineHom
  let s : S := Classical.choice inferInstance
  let a := S.fromSpecResidueField s
  let ts := (splitTorus.baseChangeIso a I).inv ≫ (baseChange a).map t
  have hts : IsClosedSubgroup ts :=
    (IsClosedSubgroup.of_iso (splitTorus.baseChangeIso a I).symm).comp (ht.baseChange a)
  exact finite_weylGroup_of_realized P (S.residueField s)
    (hG.isConnectedReductive_residueFiber s) ts hts (hP.2.2 _ a)

/-- An arbitrary full equivalence between two reduced coordinate data with
finite Weyl group can be corrected to identify any two supplied bases. -/
theorem exists_basedEquiv_of_equiv
    {I I' J J' : Type u} [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
    {P : RootDatum J (I → ℤ) (I → ℤ)}
    {Q : RootDatum J' (I' → ℤ) (I' → ℤ)} [P.IsReduced] [Q.IsReduced]
    [Finite Q.weylGroup] (b : P.Base) (c : Q.Base) (e₀ : RootPairing.Equiv P Q) :
    ∃ e : RootPairing.Equiv P Q, ∀ a,
      a ∈ b.support ↔ e.indexEquiv a ∈ c.support := by
  classical
  let ν := BasedBorelExponent.positiveCorootSum P b
  let ρQ := BasedBorelExponent.positiveCorootSum Q c
  have hposP (a : J) : 0 < P.root' a ν ↔ b.IsPos a := by
    change 0 < P.toLinearMap (P.root a) ν ↔ _
    rw [BasedBorelExponent.pairing_root_positiveCorootSum, RootPairing.Base.isPos_iff]
    omega
  have hposQ (a : J') : 0 < Q.root' a ρQ ↔ c.IsPos a := by
    change 0 < Q.toLinearMap (Q.root a) ρQ ↔ _
    rw [BasedBorelExponent.pairing_root_positiveCorootSum, RootPairing.Base.isPos_iff]
    omega
  have hν (a : J) : P.root' a ν ≠ 0 :=
    BasedBorelExponent.pairing_root_positiveCorootSum_ne_zero P b a
  have hρQ (a : J') : Q.root' a ρQ ≠ 0 :=
    BasedBorelExponent.pairing_root_positiveCorootSum_ne_zero Q c a
  let g := e₀.coweightEquiv.symm ν
  have hg (a : J') : Q.root' a g ≠ 0 := by
    obtain ⟨j, rfl⟩ := e₀.indexEquiv.surjective a
    rw [e₀.root'_coweightEquiv]
    exact hν j
  obtain ⟨w, hw⟩ := Langlands.LinearAlgebra.RootDatumWeylChambers.exists_same_signs
    Q Set.univ hρQ hg
  refine ⟨w.val.symm.comp e₀, mem_support_iff_of_isPos b c _ (fun a => ?_)⟩
  change c.IsPos (w.val.indexEquiv.symm (e₀.indexEquiv a)) ↔ b.IsPos a
  have hs := hw (w.val.indexEquiv.symm (e₀.indexEquiv a)) (Set.mem_univ _)
  have hr := w.val.root'_coweightEquiv (w.val.indexEquiv.symm (e₀.indexEquiv a))
    (w.val.coweightEquiv g)
  rw [LinearEquiv.symm_apply_apply, Equiv.apply_symm_apply] at hr
  rw [← hposQ, hs, ← hr, e₀.root'_coweightEquiv, hposP]

end CoordinateRootDatum

section GlobalBasedComparison

variable {S : Scheme.{u}} [Nonempty S]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
  {G H : GroupScheme S} (hG : IsReductive G) (hH : IsReductive H)
  {i : splitTorus S I ⟶ G} {j : splitTorus S I' ⟶ H}
  (hj : IsClosedSubgroup j)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)} [P.IsReduced] [Q.IsReduced]
  (hP : letI := hG.isAffineHom; CoordinateRootDatum.IsGlobalCoordinateRootDatumOf I G i P)
  (hQ : letI := hH.isAffineHom; CoordinateRootDatum.IsGlobalCoordinateRootDatumOf I' H j Q)
  (b : P.Base) (c : Q.Base)
  (hloc : ∃ 𝒱 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
    ∀ a : 𝒱.I₀, Nonempty ((baseChange (𝒱.f a)).obj G ≅
      (baseChange (𝒱.f a)).obj H))

/-- Choose a full based root-datum equivalence from an étale-local group
isomorphism, retaining both entire coordinate lattices. -/
def basedGlobalCoordinateRootDatumEquivOfEtaleLocalIso :
    {e : RootPairing.Equiv P Q //
      ∀ a, a ∈ b.support ↔ e.indexEquiv a ∈ c.support} := by
  let : Finite Q.weylGroup := CoordinateRootDatum.finite_weylGroup_of_global hH j hj Q hQ
  exact ⟨(CoordinateRootDatum.exists_basedEquiv_of_equiv b c
      (globalCoordinateRootDatumEquivOfEtaleLocalIso hG hH hmax hmax' hP hQ hloc)).choose,
    (CoordinateRootDatum.exists_basedEquiv_of_equiv b c
      (globalCoordinateRootDatumEquivOfEtaleLocalIso hG hH hmax hmax' hP hQ hloc)).choose_spec⟩

end GlobalBasedComparison

end Langlands.GroupScheme
