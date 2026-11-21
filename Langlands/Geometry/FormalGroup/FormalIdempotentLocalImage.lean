import Langlands.Geometry.FormalGroup.FormalIdempotentLaw
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Formal coordinate images on principal opens -/

noncomputable section

namespace Langlands.FormalGroup.ModuleLaw.Hom

open scoped TensorProduct

variable {O R : Type*} [CommRing O] [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ}
variable (e : Hom M M)

private theorem tangent_range_retraction (he : e.comp e = e) :
    e.tangent.rangeRestrict.comp e.tangent.range.subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  change e.tangent (x : σ → R) = x.val
  rw [← hy]
  have h := congrArg (fun f : Hom M M => f.tangent y) he
  simpa only [tangent_comp, LinearMap.comp_apply] using h

section BaseChange

variable {S : Type*} [CommRing S] [Algebra R S] [Algebra O S] [IsScalarTower O R S]

private theorem tangent_map_pointwise (x : σ → R) :
    (e.map (IsScalarTower.toAlgHom O R S)).tangent (fun i => algebraMap R S (x i)) =
      fun i => algebraMap R S (e.tangent x i) := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  funext i
  change (e.toHom.toCoordinateMap.map (algebraMap R S)).linearPart
      (fun i => algebraMap R S (x i)) i =
    algebraMap R S (e.toHom.toCoordinateMap.linearPart x i)
  simp only [CoordinateMap.linearPart_apply, CoordinateMap.linearCoeff_map, map_sum, map_mul]

private theorem tangent_map_piScalarRight [Fintype σ] [DecidableEq σ] :
    ((e.map (IsScalarTower.toAlgHom O R S)).tangent).comp
      (TensorProduct.piScalarRight R S S σ).toLinearMap =
    (TensorProduct.piScalarRight R S S σ).toLinearMap.comp (e.tangent.baseChange S) := by
  classical
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.baseChange_tmul,
      TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    have hmul (y : σ → R) :
        (fun j => y j • a) = a • (fun j => algebraMap R S (y j)) := by
      funext j
      simp only [Pi.smul_apply, Algebra.smul_def]
      exact mul_comm _ _
    rw [hmul x, hmul (e.tangent x), map_smul, e.tangent_map_pointwise]
  | add x y hx hy => simp only [map_add, hx, hy]

namespace IdempotentImage

variable {τ : Type} [Finite τ]

/-- Construct the image after coefficient extension from a basis of the
scalar extension of the actual tangent image. -/
def ofBaseChangeTangentBasis (he : e.comp e = e)
    (basis : Module.Basis τ S (S ⊗[R] e.tangent.range)) :
    Σ N : ModuleLaw O S τ, IdempotentImage (e.map (IsScalarTower.toAlgHom O R S)) N := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let : Fintype τ := Fintype.ofFinite τ
  let b := TensorProduct.piScalarRight R S S σ
  let i := e.tangent.range.subtype.baseChange S
  let r := e.tangent.rangeRestrict.baseChange S
  let j := b.toLinearMap.comp (i.comp basis.equivFun.symm.toLinearMap)
  let p := basis.equivFun.toLinearMap.comp (r.comp b.symm.toLinearMap)
  have hri : r.comp i = LinearMap.id := by
    have h := congrArg (fun z : e.tangent.range →ₗ[R] e.tangent.range => z.baseChange S)
      (e.tangent_range_retraction he)
    simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_id] using h
  have hir : i.comp r = e.tangent.baseChange S := by
    have h := congrArg (fun z : (σ → R) →ₗ[R] (σ → R) => z.baseChange S)
      e.tangent.subtype_comp_rangeRestrict
    simpa only [LinearMap.baseChange_comp] using h
  have hj : p.comp j = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change basis.equivFun (r (b.symm (b (i (basis.equivFun.symm x))))) = x
    rw [LinearEquiv.symm_apply_apply, ← LinearMap.comp_apply, hri, LinearMap.id_apply,
      LinearEquiv.apply_symm_apply]
  have hp : j.comp p = (e.map (IsScalarTower.toAlgHom O R S)).tangent := by
    apply LinearMap.ext
    intro x
    change b (i (basis.equivFun.symm (basis.equivFun (r (b.symm x))))) = _
    rw [LinearEquiv.symm_apply_apply, ← LinearMap.comp_apply, hir]
    have h := LinearMap.congr_fun (e.tangent_map_piScalarRight (S := S)) (b.symm x)
    change (e.map (IsScalarTower.toAlgHom O R S)).tangent (b (b.symm x)) =
      b ((e.tangent.baseChange S) (b.symm x)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have he' : (e.map (IsScalarTower.toAlgHom O R S)).comp (e.map (IsScalarTower.toAlgHom O R S)) =
      e.map (IsScalarTower.toAlgHom O R S) := by
    rw [← map_comp, he]
  exact ofTangentRetraction _ he' j p hj hp

end IdempotentImage

end BaseChange

namespace IdempotentImage

set_option backward.isDefEq.respectTransparency false in
/-- At each point of the affine base the actual projector has formal coordinates
on a principal open containing that point. -/
theorem exists_basicOpen (he : e.comp e = e) (x : PrimeSpectrum R) :
    ∃ a : R, a ∉ x.asIdeal ∧ ∃ n : ℕ,
      Nonempty (Σ N : ModuleLaw O (Localization.Away a) (Fin n),
        IdempotentImage (e.map (IsScalarTower.toAlgHom O R (Localization.Away a))) N) := by
  let P := e.tangent.range
  let : Module.Finite R P := Module.Finite.range _
  let : Module.Projective R P := Module.Projective.of_split P.subtype
    e.tangent.rangeRestrict (e.tangent_range_retraction he)
  let : Module.FinitePresentation R P := Module.finitePresentation_of_projective R P
  let : Module.Free (Localization.AtPrime x.asIdeal) (LocalizedModule.AtPrime x.asIdeal P) :=
    (Module.mem_freeLocus (R := R) (M := P) (p := x)).mp (by
      rw [Module.freeLocus_eq_univ]
      exact Set.mem_univ x)
  let : Nontrivial (Localization.AtPrime x.asIdeal) := IsLocalization.AtPrime.nontrivial _ x.asIdeal
  let stalkBasis := Module.finBasis (Localization.AtPrime x.asIdeal)
    (LocalizedModule.AtPrime x.asIdeal P)
  obtain ⟨a, ha, openBasis, _⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    (M := ↥P) (M' := LocalizedModule.AtPrime x.asIdeal P)
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl P)
      (Localization.AtPrime x.asIdeal) stalkBasis
  let basis := openBasis.map (LocalizedModule.isBaseChange (Submonoid.powers a) P).equiv.symm
  exact ⟨a, ha, _, ⟨ofBaseChangeTangentBasis e he basis⟩⟩

end IdempotentImage

end Langlands.FormalGroup.ModuleLaw.Hom
