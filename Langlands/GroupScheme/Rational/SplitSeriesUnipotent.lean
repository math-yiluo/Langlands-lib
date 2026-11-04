import Langlands.GroupScheme.Rational.VectorGroupUnipotent
import Langlands.GroupScheme.Reductive.UnipotentExtension

/-! # Coefficient-representation unipotence from an affine finite Ga-series -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section Zero

variable {B : Scheme.{u}} {H : GroupScheme B}

/-- A length-zero split series makes every point the identity on every test. -/
theorem HasSplitSeries.eq_one_of_length_zero (h : HasSplitSeries 0 H)
    {T : Over B} (x : T ⟶ H.X) : x = 1 := by
  have hx : x ∈ (SubgroupFunctor.range (𝟙 H)).carrier T :=
    SubgroupFunctor.mem_range.mpr ⟨x, by
      change x ≫ 𝟙 H.X = x
      exact Category.comp_id _⟩
  rw [h, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
  exact hx

/-- The natural zero-dimensional coordinate maps supplied by a length-zero
series, without any geometric hypothesis or restriction on the base. -/
def HasSplitSeries.zeroVectorCoordinates (h : HasSplitSeries 0 H) (T : Over B) :
    (T ⟶ H.X) ≃* Multiplicative (Fin 0 → Γ(T.left, ⊤)) where
  toFun _ := Multiplicative.ofAdd (fun i => Fin.elim0 i)
  invFun _ := 1
  left_inv x := (h.eq_one_of_length_zero x).symm
  right_inv _ := by
    apply Multiplicative.toAdd.injective
    funext i
    exact Fin.elim0 i
  map_mul' _ _ := by
    apply Multiplicative.toAdd.injective
    funext i
    exact Fin.elim0 i

/-- A length-zero series is an actual zero-dimensional vector-group witness. -/
theorem HasSplitSeries.isVectorGroupOfDimension_zero (h : HasSplitSeries 0 H) :
    IsVectorGroupOfDimension H 0 := by
  refine ⟨h.zeroVectorCoordinates, ?_⟩
  intro T W f x
  funext i
  exact Fin.elim0 i

end Zero

section Field

variable {k : Type u} [Field k]

/-- A finite normal Ga-series in an affine group implies unipotence in the
actual coefficient-representation sense. -/
theorem HasSplitSeries.isUnipotent {n : ℕ}
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (h : HasSplitSeries n H) : IsUnipotent H := by
  induction n generalizing H with
  | zero => exact h.isVectorGroupOfDimension_zero.isUnipotent
  | succ n ih =>
    obtain ⟨K, V, j, q, hj, _, _, _, hq, hV, hK⟩ := h
    let : IsClosedImmersion j.hom.hom.left := hj
    let : Mono j.hom.hom := Over.mono_of_mono_left _
    let : IsAffineHom K.X.hom := hj.isAffineHom
    have huK : IsUnipotent K := ih hK
    let hjrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
      ⟨inferInstance, rfl⟩
    let e : K ≅ kernel q :=
      hjrep.isoOfIsRepresentedBy ⟨inferInstance, hq.2.2.2⟩
    let : IsAffineHom (kernel q).X.hom :=
      isAffineHom_of_over_iso
        (((Grp.forget _).mapIso e.symm) : (kernel q).X ≅ K.X)
        (inferInstance : IsAffineHom K.X.hom)
    let : IsAffineHom V.X.hom := hV.isAffineHom
    let : Flat q.hom.hom.left := hq.1
    let : Surjective q.hom.hom.left := hq.2.1
    let : QuasiCompact (q.hom.hom.left ≫ V.X.hom) := by
      rw [Over.w q.hom.hom]
      infer_instance
    let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ V.X.hom
    exact isUnipotent_of_kernel_of_quotient q
      (IsUnipotent.of_iso e.symm huK) hV.isUnipotent

/-- An affine split-unipotent group satisfies coefficient-representation
unipotence over its original ground field. -/
theorem IsSplitUnipotent.isUnipotent
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (h : IsSplitUnipotent H) : IsUnipotent H := by
  obtain ⟨n, hn⟩ := h
  exact hn.isUnipotent

end Field

end Langlands.GroupScheme.RelativeRoot
