import Langlands.Representation.FiniteGeneralLinear.CuspidalFiniteModels
import Langlands.Representation.FiniteGeneralLinear.FiniteProductIrreducibles
import Langlands.Representation.FiniteGeneralLinear.WhittakerHeredity
import Langlands.Representation.CuspidalSupport.LeviSplitContraction
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof

/-! Exhaustion of finite irreducibles by induction from cuspidal Levi data. -/

noncomputable section

open Module Representation
open scoped BigOperators TensorProduct

namespace Langlands.FiniteGeneralLinear

open FiniteRep GeneralLinear Geometric

/-- An ordered Levi shape equipped with a cuspidal isomorphism class in every block. -/
structure HarishChandraDatum (n : ℕ) (k : Type*) [Field k] where
  shape : BlockShape n
  label : ∀ i : Fin shape.length, CuspidalModelClass (shape.size i) k

variable {k : Type*} [Field k] {n : ℕ}

/-- The external tensor of the chosen cuspidal representatives. -/
def HarishChandraDatum.leviRep (D : HarishChandraDatum n k) : FDRep ℂ (D.shape.Levi k) :=
  externalRep (fun i => VirtualCharacter.rep (D.label i).val)

/-- The finite Harish–Chandra induction attached to the datum. -/
def HarishChandraDatum.induced [Finite k] (D : HarishChandraDatum n k) : FDRep ℂ (GeneralLinear n k) :=
  harishChandraInduce D.shape D.leviRep

private abbrev radicalFixedSubmodule (B : BlockShape n) (W : FDRep ℂ (GeneralLinear n k)) :
    Submodule ℂ W :=
  invariants ((W.ρ.comp (B.parabolic k).subtype).comp (B.unipotentRadical k).subtype)

/-- The finite-dimensional Levi action on the vectors fixed by its parabolic radical. -/
def radicalFixedRep (B : BlockShape n) (W : FDRep ℂ (GeneralLinear n k)) : FDRep ℂ (B.Levi k) :=
  FDRep.of ((Representation.toInvariants (W.ρ.comp (B.parabolic k).subtype)
    (B.unipotentRadical k)).comp (B.leviInParabolic k))

private theorem exists_max_radicalFixedRep (W : FDRep ℂ (GeneralLinear n k))
    (hW : IsIrreducible W.ρ) :
    ∃ B : BlockShape n, finrank ℂ (radicalFixedRep B W) ≠ 0 ∧
      ∀ C : BlockShape n, finrank ℂ (radicalFixedRep C W) ≠ 0 → C.length ≤ B.length := by
  classical
  let P (r : ℕ) := ∃ B : BlockShape n, B.length = r ∧ finrank ℂ (radicalFixedRep B W) ≠ 0
  obtain ⟨B₀, hB₀⟩ := BlockShape.exists_length_le_one n
  obtain ⟨v, hv⟩ := FiniteIndexRestriction.exists_ne_zero W.ρ hW
  let v₀ : radicalFixedRep B₀ W := ⟨v, fun u => by
    change W.ρ u.val.val v = v
    rw [B₀.unipotentRadical_val_eq_one k hB₀ u, map_one, Module.End.one_apply]⟩
  have hr₀ : finrank ℂ (radicalFixedRep B₀ W) ≠ 0 := by
    apply ne_of_gt (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v₀, fun h => ?_⟩)
    exact hv (congrArg Subtype.val h)
  obtain ⟨B, hB, hd⟩ := Nat.findGreatest_spec (P := P) B₀.length_le ⟨B₀, rfl, hr₀⟩
  exact ⟨B, hd, fun C hC => hB ▸ Nat.le_findGreatest C.length_le ⟨C, rfl, hC⟩⟩

private theorem tprod_ne_zero {ι : Type} [Fintype ι] {X : ι → Type}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, FiniteDimensional ℂ (X i)]
    (v : ∀ i, X i) (hv : ∀ i, v i ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  classical
  let b (i : ι) := Module.finBasis ℂ (X i)
  have h_i (i : ι) : ∃ j, (b i).repr (v i) j ≠ 0 := by
    by_contra! h
    apply hv i
    apply (b i).repr.injective
    exact Finsupp.ext fun j => by simpa using h j
  choose j hj using h_i
  intro h
  have he := congrArg (fun x => (Basis.piTensorProduct b).repr x j) h
  simp only [Basis.piTensorProduct_repr_tprod_apply, map_zero, Finsupp.zero_apply] at he
  exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hj i)) he

section Exhaustion

variable [Finite k]

/-- Each finite-field irreducible occurs in induction from a cuspidal Levi tensor. -/
theorem exists_harishChandraDatum (W : FDRep ℂ (GeneralLinear n k)) (hW : IsIrreducible W.ρ) :
    ∃ D : HarishChandraDatum n k, finrank ℂ (IntertwiningMap D.induced.ρ W.ρ) ≠ 0 := by
  classical
  let : Fintype (GeneralLinear n k) := Fintype.ofFinite _
  obtain ⟨B, hB, hmax⟩ := exists_max_radicalFixedRep W hW
  let L := B.Levi k
  let R := radicalFixedRep B W
  let : Fintype L := Fintype.ofFinite L
  let : ∀ i : Fin B.length, Fintype (GeneralLinear (B.size i) k) := fun _ => Fintype.ofFinite _
  obtain ⟨T, hT⟩ := FiniteCharacter.exists_isAtom R.ρ hB
  let A : FDRep ℂ L := FDRep.of T.toRepresentation
  have hA : IsIrreducible A.ρ := FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom T hT
  obtain ⟨a, ⟨e⟩⟩ := exists_externalRep_equiv A hA
  let V (i : Fin B.length) := VirtualCharacter.rep (a i)
  let X := externalRep V
  let f : X →ₗ[ℂ] W :=
    (radicalFixedSubmodule B W).subtype.comp
      (T.toSubmodule.subtype.comp e.symm.toLinearEquiv.toLinearMap)
  have hfinj : Function.Injective f :=
    Subtype.val_injective.comp (Subtype.val_injective.comp e.symm.toLinearEquiv.injective)
  have hfLevi (m : L) (x : X) : f (X.ρ m x) = W.ρ (B.leviEmbedding k m) (f x) := by
    have he := IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap m x
    exact congrArg (fun y : T.toSubmodule => Subtype.val (Subtype.val y)) he
  have hfFixed (u : B.unipotentRadical k) (x : X) : W.ρ u.val.val (f x) = f x :=
    (Subtype.val (e.symm x)).property u
  have hfParabolic (p : B.parabolic k) (x : X) :
      f (X.ρ (B.leviProjection k p) x) = W.ρ p.val (f x) := by
    let u := B.unipotentPart k p
    let m := B.leviProjection k p
    have hp : p.val = u.val.val * (B.leviInParabolic k m).val :=
      congrArg Subtype.val ((B.decomposition k).left_inv p).symm
    rw [hp, map_mul, Module.End.mul_apply]
    change f (X.ρ m x) = W.ρ u.val.val (W.ρ (B.leviEmbedding k m) (f x))
    rw [← hfLevi, hfFixed]
  have hCusp (i : Fin B.length) : IsCuspidal (V i).ρ := by
    intro C hC v hv
    by_contra hv₀
    let S : BlockRefinement B := Function.update
      (fun j => CuspidalSupport.LeviAdmissibility.oneBlock (B.size j) (B.positive j)) i C
    have hSi : S i = C := Function.update_self _ _ _
    have hSj (j) (hj : j ≠ i) :
        S j = CuspidalSupport.LeviAdmissibility.oneBlock (B.size j) (B.positive j) :=
      Function.update_of_ne hj ..
    have hS : refinedParabolic k B S ≠ ⊤ := by
      intro he
      apply hC
      rw [eq_top_iff]
      intro p _
      have hm : (Pi.mulSingle i p : B.Levi k) ∈ refinedParabolic k B S := he ▸ Subgroup.mem_top _
      have hm' := (mem_refinedParabolic k B S _).mp hm i
      rwa [hSi, Pi.mulSingle_eq_same] at hm'
    have hlt := B.length_lt_flatten S k hS
    have he (j : Fin B.length) : ∃ w : V j, w ≠ 0 :=
      FiniteIndexRestriction.exists_ne_zero _ (VirtualCharacter.isIrreducible_rep (a j))
    choose w hw using he
    let z := Function.update w i v
    have hz (j : Fin B.length) : z j ≠ 0 := by
      by_cases hj : j = i
      · subst j
        simpa only [z, Function.update_self] using hv₀
      · simpa only [z, Function.update_of_ne hj] using hw j
    let y : X := PiTensorProduct.tprod ℂ z
    have hy : y ≠ 0 := tprod_ne_zero z hz
    have hfy : f y ≠ 0 := by
      intro he
      exact hy (hfinj (he.trans (map_zero f).symm))
    have hflat : finrank ℂ (radicalFixedRep (B.flatten S) W) ≠ 0 := by
      let v' : radicalFixedRep (B.flatten S) W := ⟨f y, fun u => by
        let g : GeneralLinear n k := u.val.val
        have hg : g ∈ (B.flatten S).unipotentSubgroup k := ⟨u.val, u.property, rfl⟩
        have hmem := B.flatten_unipotentSubgroup_le S k hg
        obtain ⟨hp, hproj⟩ := (Parabolic.mem_leviPreimage_iff k B _ g).mp hmem
        let p : B.parabolic k := ⟨g, hp⟩
        have hcoords := (mem_refinedUnipotent k B S _).mp hproj
        have hzy : X.ρ (B.leviProjection k p) y = y := by
          change FiniteTensor.external (fun j => (V j).ρ) _ (PiTensorProduct.tprod ℂ z) = _
          rw [FiniteTensor.external_tprod]
          apply congrArg (PiTensorProduct.tprod ℂ)
          funext j
          by_cases hj : j = i
          · subst j
            have hi := hcoords i
            rw [hSi] at hi
            have hz' : z i = v := Function.update_self i v w
            rw [hz']
            exact hv _ hi
          · have hi := hcoords j
            rw [hSj j hj] at hi
            have hh : B.leviProjection k p j = 1 :=
              CuspidalSupport.LeviAdmissibility.eq_one_of_mem_oneBlock_unipotent _ hi
            rw [hh, map_one, Module.End.one_apply]
        change W.ρ p.val (f y) = f y
        rw [← hfParabolic, hzy]⟩
      apply ne_of_gt (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v', fun h => ?_⟩)
      exact hfy (congrArg Subtype.val h)
    exact (not_lt_of_ge (hmax (B.flatten S) hflat)) hlt
  let D : HarishChandraDatum n k := ⟨B, fun i => ⟨a i, hCusp i⟩⟩
  refine ⟨D, ?_⟩
  let P := B.parabolic k
  let E := pullbackRep (B.leviProjection k) X
  change finrank ℂ (IntertwiningMap (induceRep P E).ρ W.ρ) ≠ 0
  rw [finrank_intertwiningMap_induceRep_left]
  let F : IntertwiningMap E.ρ (W.ρ.comp P.subtype) :=
    { toLinearMap := f
      isIntertwining' := fun p => LinearMap.ext fun x => hfParabolic p x }
  have hF : F ≠ 0 := by
    have hX : IsIrreducible X.ρ :=
      isIrreducible_externalRep V (fun i => VirtualCharacter.isIrreducible_rep (a i))
    obtain ⟨x, hx⟩ := FiniteIndexRestriction.exists_ne_zero X.ρ hX
    intro he
    exact hx (hfinj ((congrArg (fun m : IntertwiningMap E.ρ (W.ρ.comp P.subtype) => m x) he).trans
      (map_zero f).symm))
  exact ne_of_gt (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨F, hF⟩)

end Exhaustion

end Langlands.FiniteGeneralLinear
