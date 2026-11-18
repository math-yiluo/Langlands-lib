import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Generation
import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Torus
import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Smooth
import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.BaseChange
import Langlands.GroupScheme.SymplecticMatrix.Reductive

/-! # Connectedness of the split Cayley automorphism group scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitCayley

theorem isAutomorphism_map_ringEquiv {A B : Type u} [CommRing A] [CommRing B] (f : A ≃+* B)
    {M : Matrix (Fin 8) (Fin 8) A} (hM : IsAutomorphism M.mulVec) :
    IsAutomorphism (M.map f).mulVec := by
  have key : ∀ y : Fin 8 → B,
      (M.map f) *ᵥ y = fun i => f ((M *ᵥ fun j => f.symm (y j)) i) := by
    intro y
    funext i
    have h := RingHom.map_mulVec (f : A →+* B) M (fun j => f.symm (y j)) i
    simpa [Function.comp_def] using h.symm
  have hsymm : ∀ x y : Fin 8 → B, (fun i => f.symm (mulFun B x y i)) =
      mulFun A (fun i => f.symm (x i)) (fun i => f.symm (y i)) :=
    fun x y => map_mulFun B (f.symm : B →+* A) x y
  refine ⟨?_, fun x y => ?_⟩
  · rw [key]
    have hu : (fun j => f.symm (unit B j)) = unit A := by
      funext j
      fin_cases j <;> simp [unit]
    rw [hu, hM.1]
    funext j
    fin_cases j <;> simp [unit]
  · rw [key, key, key, hsymm, hM.2]
    exact map_mulFun A (f : A →+* B) _ _

section Connected

variable {k : Type u} [Field k]

/-- Over an algebraically closed field the automorphism group scheme of Zorn's split Cayley
algebra is connected. -/
theorem connectedSpace_automorphismGroup_of_isAlgClosed [IsAlgClosed k] :
    ConnectedSpace (CayleyDatum.split k).automorphismGroup.X.left := by
  have : Smooth (CayleyDatum.split k).automorphismGroup.X.hom := smooth_automorphismGroup
  refine IdentityComponent.connectedSpace_of_forall_mem_range fun x => ?_
  let T₀ : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  let e : k ≃+* Γ(T₀.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  let R := (SubgroupFunctor.range
    (identityComponentι (CayleyDatum.split k).automorphismGroup)).carrier T₀
  let P : Subgroup (GL (Fin 8) Γ(T₀.left, ⊤)) :=
    R.map (((CayleyDatum.split k).automorphismSubgroup (scalarMap T₀)).subtype.comp
      (pointsEquiv k T₀).toMonoidHom)
  have hroot : ∀ (α : Root) (c : Γ(T₀.left, ⊤)), rootGL α c ∈ P := by
    intro α c
    let y : T₀ ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X :=
      (VectorGroup.coordinates _ 1 T₀).symm (Multiplicative.ofAdd fun _ => c)
    refine ⟨y ≫ (rootMap k α).hom.hom,
      SymplecticMatrix.comp_mem_range_identityComponentι (rootMap k α) y, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype, pointsEquiv_rootMap, coe_rootHom, y, MulEquiv.apply_symm_apply,
      toAdd_ofAdd]
  have htorus : ∀ s t : Γ(T₀.left, ⊤)ˣ, torusGL s t ∈ P := by
    intro s t
    have := IsSplitTorus.connectedSpace (isSplitTorus_torus k)
    let y : T₀ ⟶ (splitTorus (Spec (CommRingCat.of k)) (ULift.{u} (Fin 2))).X :=
      (splitTorus.pointsEquiv (ULift.{u} (Fin 2)) T₀).symm (fun i => ![s, t] i.down)
    refine ⟨y ≫ (torusMap k).hom.hom,
      SymplecticMatrix.comp_mem_range_identityComponentι (torusMap k) y, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype, pointsEquiv_torusMap, coe_torusHom, y, MulEquiv.apply_symm_apply]
    rfl
  have hcl : (rootTorusClosure k).map (GeneralLinearGroup.map (e : k →+* Γ(T₀.left, ⊤))) ≤ P := by
    rw [Subgroup.map_le_iff_le_comap, rootTorusClosure, Subgroup.closure_le]
    rintro _ (⟨⟨α, r⟩, rfl⟩ | ⟨⟨s, t⟩, rfl⟩)
    · refine Subgroup.mem_comap.2 ?_
      change GeneralLinearGroup.map _ (rootGL α r) ∈ P
      rw [rootGL_map]
      exact hroot α _
    · refine Subgroup.mem_comap.2 ?_
      change GeneralLinearGroup.map _ (torusGL s t) ∈ P
      rw [torusGL_map]
      exact htorus _ _
  let g : GL (Fin 8) Γ(T₀.left, ⊤) := pointsEquiv k T₀ x
  have hg : IsAutomorphism (g : Matrix (Fin 8) (Fin 8) Γ(T₀.left, ⊤)).mulVec :=
    (mem_automorphismSubgroup_split_iff _ _).1 (pointsEquiv k T₀ x).2
  let g₀ : GL (Fin 8) k := GeneralLinearGroup.map (e.symm : Γ(T₀.left, ⊤) →+* k) g
  have hg₀ : IsAutomorphism (g₀ : Matrix (Fin 8) (Fin 8) k).mulVec :=
    isAutomorphism_map_ringEquiv e.symm hg
  have hmem := hcl ⟨g₀, mem_rootTorusClosure hg₀, rfl⟩
  have hgg : GeneralLinearGroup.map (e : k →+* Γ(T₀.left, ⊤)) g₀ = g := by
    ext i j
    simp [g₀]
  rw [hgg] at hmem
  obtain ⟨y, hy, hyx⟩ := hmem
  have hyx' : y = x := (pointsEquiv k T₀).injective (Subtype.ext hyx)
  rwa [← hyx']

variable (k) in
/-- The automorphism group scheme of Zorn's split Cayley algebra over a field is connected. -/
theorem connectedSpace_automorphismGroup :
    ConnectedSpace (CayleyDatum.split k).automorphismGroup.X.left := by
  let b := toAlgebraicClosure k
  have : Surjective b := (fieldExtension_fpqc k (AlgebraicClosure k)).1
  refine connectedSpace_of_baseChange b _ ?_
  have : ConnectedSpace (CayleyDatum.split (AlgebraicClosure k)).automorphismGroup.X.left :=
    connectedSpace_automorphismGroup_of_isAlgClosed
  exact DynamicConnected.connectedSpace_of_iso (baseChangeModelIso b)

end Connected

end SplitCayley

end Langlands.GroupScheme
