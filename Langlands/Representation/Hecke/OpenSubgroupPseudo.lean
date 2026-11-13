import Langlands.Representation.Hecke.OpenSubgroupHeckeBasics
import Langlands.Representation.Hecke.NormalQuotientPseudo

/-! # Pseudo-forgetting for an open subgroup -/

noncomputable section

open CategoryTheory MeasureTheory MulOpposite

namespace Langlands.Hecke.Homomorphism.OpenSubgroup

open HarmonicAnalysis Langlands.Algebra

universe uG v

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) (hH : IsOpen (H : Set G)) [LocallyCompactSpace H]
  (μG : Measure G) [μG.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]
  (V : NondegenerateModuleCat.{uG, v} (HeckeAlgebra μG))

/-- The contraction of the forgetful tensor, followed by `c`, intertwines the
left `H(H)`-action with the right `H(H)`-action on `c`. -/
theorem smul_contraction_smul (a : HeckeAlgebra μH) (c : HeckeAlgebra μG)
    (t : ((F μG μH H.subtype continuous_subtype_val).obj V).obj) :
    c • RegularTensorContraction.contraction (HeckeAlgebra μG) V.obj (a • t) =
      (letI := rightModule μG μH H.subtype continuous_subtype_val
       op a • c) • RegularTensorContraction.contraction (HeckeAlgebra μG) V.obj t := by
  let _ := NonUnitalModule.rightRegular (HeckeAlgebra μG)
  let lhs : ((F μG μH H.subtype continuous_subtype_val).obj V).obj →+ V.obj :=
    ((NonUnitalModule.toEndHom V.obj.isModule c).comp
      (RegularTensorContraction.contraction (HeckeAlgebra μG) V.obj)).comp
      (NonUnitalModule.toEndHom
        ((F μG μH H.subtype continuous_subtype_val).obj V).obj.isModule a)
  let rhs : ((F μG μH H.subtype continuous_subtype_val).obj V).obj →+ V.obj :=
    (NonUnitalModule.toEndHom V.obj.isModule
      (letI := rightModule μG μH H.subtype continuous_subtype_val
       op a • c)).comp
      (RegularTensorContraction.contraction (HeckeAlgebra μG) V.obj)
  have h : lhs = rhs := by
    apply NonUnitalModuleTensor.hom_ext (HeckeAlgebra μG)
    intro b m
    change c • ((letI := leftModule μG μH H.subtype continuous_subtype_val
      a • b) • m) = (letI := rightModule μG μH H.subtype continuous_subtype_val
       op a • c) • (b • m)
    rw [← mul_smul, ← mul_smul,
      rightModule_mul μG μH H.subtype continuous_subtype_val]
  exact DFunLike.congr_fun h t

/-- Every regular orbit of a contracted tensor is in the pseudo-forgetful part. -/
theorem regularOrbit_contraction_mem
    (t : ((F μG μH H.subtype continuous_subtype_val).obj V).obj) :
    regularOrbit (RegularTensorContraction.contraction (HeckeAlgebra μG) V.obj t) ∈
      (letI := rightModule μG μH H.subtype continuous_subtype_val
       RenardHomFunctors.pseudoPart
        (regular_commutes_right μG μH H.subtype continuous_subtype_val)
        (isIdempotented μH) V.obj) := by
  let _ := rightModule μG μH H.subtype continuous_subtype_val
  obtain ⟨e, he⟩ := ((F μG μH H.subtype continuous_subtype_val).obj V).property t
  refine (RenardHomFunctors.mem_pseudoPart _ _ _).mpr ⟨e, fun b => ?_⟩
  change (op (e : HeckeAlgebra μH) • b) •
      RegularTensorContraction.contraction (HeckeAlgebra μG) V.obj t =
    b • RegularTensorContraction.contraction (HeckeAlgebra μG) V.obj t
  rw [← smul_contraction_smul H μG μH V, he]

/-- The comparison `F V → pseudoF V`, `t ↦ (c ↦ c • contraction t)`. -/
def forgetToPseudo :
    (F μG μH H.subtype continuous_subtype_val).obj V ⟶
      (pseudoF μG μH H.subtype continuous_subtype_val).obj V :=
  ObjectProperty.homMk
    { toFun := fun t => ⟨regularOrbit (RegularTensorContraction.contraction
        (HeckeAlgebra μG) V.obj t), regularOrbit_contraction_mem H μG μH V t⟩
      map_zero' := by
        let _ := NonUnitalModule.regular (HeckeAlgebra μG)
        apply Subtype.ext
        apply NonUnitalModuleHom.ext
        intro c
        change c • RegularTensorContraction.contraction (HeckeAlgebra μG) V.obj 0 = 0
        rw [map_zero, smul_zero]
      map_add' := fun s t => by
        let _ := NonUnitalModule.regular (HeckeAlgebra μG)
        apply Subtype.ext
        apply NonUnitalModuleHom.ext
        intro c
        change c • RegularTensorContraction.contraction (HeckeAlgebra μG) V.obj (s + t) =
          c • RegularTensorContraction.contraction (HeckeAlgebra μG) V.obj s +
            c • RegularTensorContraction.contraction (HeckeAlgebra μG) V.obj t
        exact (congrArg (c • ·)
          (map_add (RegularTensorContraction.contraction (HeckeAlgebra μG) V.obj) s t)).trans
          (smul_add c _ _)
      map_smul' := fun a t => by
        let _ := NonUnitalModule.regular (HeckeAlgebra μG)
        apply Subtype.ext
        apply NonUnitalModuleHom.ext
        intro c
        exact smul_contraction_smul H μG μH V a c t }

theorem forgetToPseudo_apply
    (t : ((F μG μH H.subtype continuous_subtype_val).obj V).obj)
    (c : HeckeAlgebra μG) :
    (letI := NonUnitalModule.regular (HeckeAlgebra μG)
     show NonUnitalModuleHom (HeckeAlgebra μG) (HeckeAlgebra μG) V.obj from
      ((forgetToPseudo H μG μH V).hom.toAddMonoidHom t).val) c =
      c • RegularTensorContraction.contraction (HeckeAlgebra μG) V.obj t := rfl

include hH in
/-- The comparison is bijective: injectivity uses the contraction and the
nondegeneracy of `V`; surjectivity uses the image of a subgroup local unit
in the ambient Hecke algebra. -/
theorem forgetToPseudo_bijective :
    Function.Bijective (forgetToPseudo H μG μH V).hom.toAddMonoidHom := by
  let _ := NonUnitalModule.regular (HeckeAlgebra μG)
  let _ := rightModule μG μH H.subtype continuous_subtype_val
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro t ht
    have hc (c : HeckeAlgebra μG) :
        c • RegularTensorContraction.contraction (HeckeAlgebra μG) V.obj t = 0 :=
      congrArg (fun ψ : ((pseudoF μG μH H.subtype
          continuous_subtype_val).obj V).obj =>
        (show NonUnitalModuleHom (HeckeAlgebra μG) (HeckeAlgebra μG) V.obj from ψ.val) c) ht
    obtain ⟨e, he⟩ := V.property (RegularTensorContraction.contraction (HeckeAlgebra μG) V.obj t)
    apply RegularTensorContraction.contraction_injective (HeckeAlgebra μG) V.obj
      (isIdempotented μG)
    exact he.symm.trans ((hc _).trans (map_zero _).symm)
  · intro x
    let ψ : NonUnitalModuleHom (HeckeAlgebra μG) (HeckeAlgebra μG) V.obj := x.val
    obtain ⟨e, he⟩ := (RenardHomFunctors.mem_pseudoPart _ _ ψ).mp x.property
    set eG := openHeckeLinear H hH μG μH (e : HeckeAlgebra μH)
    have hb (b : HeckeAlgebra μG) : ψ b = b • ψ eG := by
      calc
        ψ b = ψ (op (e : HeckeAlgebra μH) • b) := (he b).symm
        _ = ψ (b * eG) := by rw [open_rightModule_eq H hH μG μH]
        _ = b • ψ eG := ψ.map_smul b eG
    obtain ⟨f, hf⟩ := V.property (ψ eG)
    refine ⟨RegularTensorContraction.pure (HeckeAlgebra μG) V.obj (f : HeckeAlgebra μG) (ψ eG),
      ?_⟩
    apply Subtype.ext
    apply NonUnitalModuleHom.ext
    intro c
    change c • ((f : HeckeAlgebra μG) • ψ eG) = ψ c
    rw [hf, hb c]

/-- Naturality of the comparison, from naturality of the contraction. -/
theorem forgetToPseudo_naturality {V W : NondegenerateModuleCat.{uG, v} (HeckeAlgebra μG)}
    (f : V ⟶ W) :
    (F μG μH H.subtype continuous_subtype_val).map f ≫
        forgetToPseudo H μG μH W =
      forgetToPseudo H μG μH V ≫
        (pseudoF μG μH H.subtype continuous_subtype_val).map f := by
  let _ := NonUnitalModule.regular (HeckeAlgebra μG)
  let _ := NonUnitalModule.rightRegular (HeckeAlgebra μG)
  let g : NonUnitalModuleHom (HeckeAlgebra μG) V.obj W.obj := f.hom
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  intro t
  apply Subtype.ext
  apply NonUnitalModuleHom.ext
  intro c
  change c • RegularTensorContraction.contraction (HeckeAlgebra μG) W.obj
      (RegularTensorContraction.tensorMap (HeckeAlgebra μG) g t) =
    g (c • RegularTensorContraction.contraction (HeckeAlgebra μG) V.obj t)
  rw [g.map_smul]
  exact congrArg (c • ·) (DFunLike.congr_fun
    (RegularTensorContraction.contraction_naturality (HeckeAlgebra μG) g) t)

/-- For an open subgroup, pseudo-forgetting is naturally isomorphic to forgetting. -/
def pseudoFIsoF :
    pseudoF.{uG, uG, v} μG μH H.subtype continuous_subtype_val ≅
      F.{uG, uG, v} μG μH H.subtype continuous_subtype_val :=
  (NatIso.ofComponents
    (fun V => nondegenerateIsoOfBijective (forgetToPseudo H μG μH V)
      (forgetToPseudo_bijective H hH μG μH V))
    (fun f => forgetToPseudo_naturality H μG μH f)).symm

end Langlands.Hecke.Homomorphism.OpenSubgroup
