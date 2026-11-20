import Langlands.Geometry.FormalGroup.RationalTorsionSimilitudeCoherence
import Langlands.Geometry.FormalGroup.FiniteKernelComposition

/-! # Restriction and composition of local rational torsion similitudes -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {L : ModuleLaw O R υ}
variable {π : O} {hM : M.IsPiDivisible π} {hN : N.IsPiDivisible π}

set_option maxHeartbeats 800000 in
private theorem overAlgebraIso_isometry (P : TorsionPrincipalPolarization hM)
    {A B : CommAlgCat.{v} R} (j : A ⟶ B) :
    (M.overAlgebraIso j).hom.IsTorsionSimilitude
      ((P.baseChange (IsScalarTower.toAlgHom O R A)).baseChange (coefficientAlgHom j))
      (P.baseChange (IsScalarTower.toAlgHom O R B)) 1 := by
  let α := IsScalarTower.toAlgHom O R A
  let β := IsScalarTower.toAlgHom O R B
  let ψ := coefficientAlgHom (O := O) j
  let idB := AlgHom.id O B
  have h : ψ.comp α = idB.comp β := AlgHom.ext j.hom.commutes
  let e := mapSquareIso M α ψ β idB h
  let i := mapIdIso (M.overAlgebra B)
  have heq : (M.overAlgebraIso j).hom = i.hom.comp e.hom := by
    apply Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id = CoordinateMap.id.comp CoordinateMap.id
    exact (CoordinateMap.id_comp _).symm
  rw [heq]
  simpa only [one_mul] using (mapIdIso_isometry (P.baseChange β)).comp
    (mapSquareIso_isometry α ψ P β idB h)

namespace Hom.IsTorsionSimilitude

variable {P : TorsionPrincipalPolarization hM} {Q : TorsionPrincipalPolarization hN}

/-- Coherent integral coefficient restriction preserves the actual multiplier. -/
theorem algebraMapLinear {A B : CommAlgCat.{v} R}
    {f : Hom (M.overAlgebra A) (N.overAlgebra A)} {a : O}
    (hf : f.IsTorsionSimilitude (P.baseChange (IsScalarTower.toAlgHom O R A))
      (Q.baseChange (IsScalarTower.toAlgHom O R A)) a) (j : A ⟶ B) :
    (Hom.algebraMapLinear j f).IsTorsionSimilitude
      (P.baseChange (IsScalarTower.toAlgHom O R B))
      (Q.baseChange (IsScalarTower.toAlgHom O R B)) a :=
  (hf.baseChange (coefficientAlgHom j)).transportIso
    (M.overAlgebraIso j) (N.overAlgebraIso j)
    (overAlgebraIso_isometry P j) (overAlgebraIso_isometry Q j)

end Hom.IsTorsionSimilitude

namespace RationalSection.HasLocalTorsionSimilitude

variable {C : Type w} [CommRing C] [Algebra C O]
variable {k : Type z} [Field k] [Algebra C k]
variable {p : C} {c d : kˣ}
variable {hM₀ : M.IsPiDivisible (algebraMap C O p)} {hN₀ : N.IsPiDivisible (algebraMap C O p)}
variable {hL₀ : L.IsPiDivisible (algebraMap C O p)}
variable {P : TorsionPrincipalPolarization hM₀} {Q : TorsionPrincipalPolarization hN₀}
variable {H : TorsionPrincipalPolarization hL₀}
variable {U V : Opens (PrimeSpectrum R)}
variable {f : RationalSection F M N U} {g : RationalSection F N L U}

private theorem restrict_presentation (n : ℕ) {W : Opens (PrimeSpectrum R)}
    (i : V ⟶ U) (j : W ⟶ V) {a : OpenIntegralHom M N V}
    (h : (algebraMap O F (algebraMap C O p)) ^ n • RationalSection.restrict i f = ofIntegral V a) :
    (algebraMap O F (algebraMap C O p)) ^ n • RationalSection.restrict (j ≫ i) f =
      ofIntegral W (Hom.algebraMapLinear ((coefficientStructurePresheaf R).map j.op) a) := by
  have h' := congrArg (RationalSection.restrict j) h
  simpa only [map_smul, ← RationalSection.restrict_comp, RationalSection.restrict_ofIntegral] using h'

/-- Restrict the witnessing integral numerators and their multiplier to a smaller open. -/
theorem restrict (hf : HasLocalTorsionSimilitude p P Q f c) (i : V ⟶ U) :
    HasLocalTorsionSimilitude p P Q (RationalSection.restrict i f) c := by
  intro x
  obtain ⟨W, hx, j, n, a, m, ha, heq, hm, hpol⟩ := hf ⟨x, leOfHom i x.property⟩
  let l : W ⊓ V ⟶ W := homOfLE inf_le_left
  let r : W ⊓ V ⟶ V := homOfLE inf_le_right
  let ψ := (coefficientStructurePresheaf R).map l.op
  refine ⟨W ⊓ V, ⟨hx, x.property⟩, r, n, Hom.algebraMapLinear ψ a, m, ha.algebraMapLinear ψ,
    ?_, hm, hpol.algebraMapLinear ψ⟩
  rw [← RationalSection.restrict_comp]
  have h : r ≫ i = l ≫ j := Subsingleton.elim _ _
  rw [h]
  exact restrict_presentation n j l heq

set_option maxHeartbeats 1000000 in
/-- Multiply rational multipliers by composing integral numerators
on the intersection of their witnessing opens. -/
theorem comp (hg : HasLocalTorsionSimilitude p Q H g d)
    (hf : HasLocalTorsionSimilitude p P Q f c) :
    HasLocalTorsionSimilitude p P H (RationalSection.comp g f) (c * d) := by
  intro x
  obtain ⟨Vf, hxf, i, n, a, s, ha, hef, hs, hpolF⟩ := hf x
  obtain ⟨Vg, hxg, j, m, b, t, hb, heg, ht, hpolG⟩ := hg x
  let W := Vf ⊓ Vg
  let l : W ⟶ Vf := homOfLE inf_le_left
  let r : W ⟶ Vg := homOfLE inf_le_right
  let inclusion : W ⟶ U := l ≫ i
  let ψf := (coefficientStructurePresheaf R).map l.op
  let ψg := (coefficientStructurePresheaf R).map r.op
  let a' := Hom.algebraMapLinear ψf a
  let b' := Hom.algebraMapLinear ψg b
  have hi : r ≫ j = inclusion := Subsingleton.elim _ _
  have hrepF : (algebraMap O F (algebraMap C O p)) ^ n • RationalSection.restrict inclusion f =
      ofIntegral W a' := restrict_presentation n i l hef
  have hrepG : (algebraMap O F (algebraMap C O p)) ^ m • RationalSection.restrict inclusion g =
      ofIntegral W b' := by
    have h := restrict_presentation m j r heg
    rwa [hi] at h
  refine ⟨W, ⟨hxf, hxg⟩, inclusion, m + n, b'.comp a', s * t,
    (hb.algebraMapLinear ψg).comp_of_finiteKernelComposition
      (Hom.finiteKernelCompositionStatement _ _ _) (ha.algebraMapLinear ψf), ?_, ?_, ?_⟩
  · rw [restrict_comp_hom, pow_add, mul_smul, ← comp_smul, ← smul_comp, hrepF, hrepG, comp_ofIntegral]
  · rw [_root_.map_mul, hs, ht, Units.val_mul, Nat.mul_add, pow_add]
    ac_rfl
  · simpa only [_root_.map_mul] using (hpolG.algebraMapLinear ψg).comp (hpolF.algebraMapLinear ψf)

end RationalSection.HasLocalTorsionSimilitude

end Langlands.FormalGroup.ModuleLaw
