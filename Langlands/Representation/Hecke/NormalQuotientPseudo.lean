import Langlands.Representation.Hecke.NormalQuotientBalance
import Langlands.Representation.Hecke.HomomorphismRight
import Langlands.Algebra.RegularTensorContraction
import Langlands.Representation.Hecke.LocalUnitsProof

/-! # Pseudo-forgetting equals forgetting for a normal quotient

Renard III.2.10, printed pp.80–82 / PDF pp.86–88.
-/

noncomputable section

open CategoryTheory MeasureTheory MulOpposite

namespace Langlands.Hecke.Homomorphism

open HarmonicAnalysis Langlands.Algebra

universe uG uH uP v

section General

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] [T2Space H]
  [NonarchimedeanGroup H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  (μG : Measure G) [μG.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]
  (φ : H →* G) (hφ : Continuous φ)

/-- The two specified `H(H)`-actions on `H(G)` are balanced against convolution:
`(T·a) * S = T * (a·S)`. -/
theorem rightModule_mul (a : HeckeAlgebra μH) (T S : HeckeAlgebra μG) :
    (letI := rightModule μG μH φ hφ; op a • T) * S =
      T * (letI := leftModule μG μH φ hφ; a • S) := by
  have h1 := heckeAction_leftTests_eq_mul μG (letI := rightModule μG μH φ hφ; op a • T) S
  have h2 := heckeAction_rightModule μG μH φ hφ (GroupAction.leftTests (G := G))
    isSmooth_leftTests a T S
  have h3 := heckeAction_leftTests_eq_mul μG T (letI := leftModule μG μH φ hφ; a • S)
  exact h1.symm.trans (h2.trans h3)

end General

/-- A bijective morphism of nondegenerate modules is an isomorphism. -/
def nondegenerateIsoOfBijective {A : Type uG} [NonUnitalRing A]
    {X Y : NondegenerateModuleCat.{uG, v} A} (f : X ⟶ Y)
    (hf : Function.Bijective f.hom.toAddMonoidHom) : X ≅ Y := by
  let E := AddEquiv.ofBijective f.hom.toAddMonoidHom hf
  refine
    { hom := f
      inv := ObjectProperty.homMk
        { toAddMonoidHom := E.symm.toAddMonoidHom
          map_smul' := ?_ }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · intro a m
    apply E.injective
    change E (E.symm (a • m)) = f.hom.toAddMonoidHom (a • E.symm m)
    rw [E.apply_symm_apply, f.hom.map_smul]
    change a • m = a • E (E.symm m)
    rw [E.apply_symm_apply]
  · apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro t
    exact E.symm_apply_apply t
  · apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    exact E.apply_symm_apply m

@[simp] theorem nondegenerateIsoOfBijective_hom {A : Type uG} [NonUnitalRing A]
    {X Y : NondegenerateModuleCat.{uG, v} A} (f : X ⟶ Y)
    (hf : Function.Bijective f.hom.toAddMonoidHom) :
    (nondegenerateIsoOfBijective f hf).hom = f := rfl

/-- The regular orbit map `b ↦ b • m`, as a map from the left regular module. -/
def regularOrbit {A : Type uG} [NonUnitalRing A] {M : Type v} [AddCommGroup M]
    [NonUnitalModule A M] (m : M) :
    @NonUnitalModuleHom A A M _ _ _ (NonUnitalModule.regular A) _ :=
  @NonUnitalModuleHom.mk _ _ _ _ _ _ (NonUnitalModule.regular A) _
    { toFun := fun b => b • m
      map_zero' := NonUnitalModule.zero_smul m
      map_add' := fun b c => NonUnitalModule.add_smul b c m }
    (fun c b => mul_smul c b m)

@[simp] theorem regularOrbit_apply {A : Type uG} [NonUnitalRing A] {M : Type v}
    [AddCommGroup M] [NonUnitalModule A M] (m : M) (b : A) :
    regularOrbit m b = b • m := rfl

section Pseudo

variable {P : Type uP} [Group P] [TopologicalSpace P] [T2Space P]
  [NonarchimedeanGroup P] [LocallyCompactSpace P] [MeasurableSpace P] [BorelSpace P]
  (N : Subgroup P) [N.Normal] [IsClosed (N : Set P)]
  [MeasurableSpace (P ⧸ N)] [BorelSpace (P ⧸ N)]
  (μP : Measure P) [μP.IsHaarMeasure]
  (μM : Measure (P ⧸ N)) [μM.IsHaarMeasure]
  (V : NondegenerateModuleCat.{uP, v} (HeckeAlgebra μM))

/-- The contraction of the forgetful tensor, followed by `c`, intertwines the
left `H(P)`-action with the right `H(P)`-action on `c`. -/
theorem smul_contraction_smul (a : HeckeAlgebra μP) (c : HeckeAlgebra μM)
    (t : ((F μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)).obj V).obj) :
    c • RegularTensorContraction.contraction (HeckeAlgebra μM) V.obj (a • t) =
      (letI := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
       op a • c) • RegularTensorContraction.contraction (HeckeAlgebra μM) V.obj t := by
  let _ := NonUnitalModule.rightRegular (HeckeAlgebra μM)
  let lhs : ((F μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)).obj V).obj →+ V.obj :=
    ((NonUnitalModule.toEndHom V.obj.isModule c).comp
      (RegularTensorContraction.contraction (HeckeAlgebra μM) V.obj)).comp
      (NonUnitalModule.toEndHom
        ((F μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)).obj V).obj.isModule a)
  let rhs : ((F μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)).obj V).obj →+ V.obj :=
    (NonUnitalModule.toEndHom V.obj.isModule
      (letI := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
       op a • c)).comp
      (RegularTensorContraction.contraction (HeckeAlgebra μM) V.obj)
  have h : lhs = rhs := by
    apply NonUnitalModuleTensor.hom_ext (HeckeAlgebra μM)
    intro b m
    change c • ((letI := leftModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
      a • b) • m) = (letI := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
       op a • c) • (b • m)
    rw [← mul_smul, ← mul_smul, rightModule_mul]
  exact DFunLike.congr_fun h t

/-- Every regular orbit of a contracted tensor is in the pseudo-forgetful part. -/
theorem regularOrbit_contraction_mem
    (t : ((F μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)).obj V).obj) :
    regularOrbit (RegularTensorContraction.contraction (HeckeAlgebra μM) V.obj t) ∈
      (letI := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
       RenardHomFunctors.pseudoPart
        (regular_commutes_right μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N))
        (isIdempotented μP) V.obj) := by
  let _ := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
  obtain ⟨e, he⟩ := ((F μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)).obj V).property t
  refine (RenardHomFunctors.mem_pseudoPart _ _ _).mpr ⟨e, fun b => ?_⟩
  change (op (e : HeckeAlgebra μP) • b) •
      RegularTensorContraction.contraction (HeckeAlgebra μM) V.obj t =
    b • RegularTensorContraction.contraction (HeckeAlgebra μM) V.obj t
  rw [← smul_contraction_smul, he]

/-- The comparison `F V → pseudoF V`, `t ↦ (c ↦ c • contraction t)`. -/
def forgetToPseudo :
    (F μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)).obj V ⟶
      (pseudoF μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)).obj V :=
  ObjectProperty.homMk
    { toFun := fun t => ⟨regularOrbit (RegularTensorContraction.contraction
        (HeckeAlgebra μM) V.obj t), regularOrbit_contraction_mem N μP μM V t⟩
      map_zero' := by
        let _ := NonUnitalModule.regular (HeckeAlgebra μM)
        apply Subtype.ext
        apply NonUnitalModuleHom.ext
        intro c
        change c • RegularTensorContraction.contraction (HeckeAlgebra μM) V.obj 0 = 0
        rw [map_zero, smul_zero]
      map_add' := fun s t => by
        let _ := NonUnitalModule.regular (HeckeAlgebra μM)
        apply Subtype.ext
        apply NonUnitalModuleHom.ext
        intro c
        change c • RegularTensorContraction.contraction (HeckeAlgebra μM) V.obj (s + t) =
          c • RegularTensorContraction.contraction (HeckeAlgebra μM) V.obj s +
            c • RegularTensorContraction.contraction (HeckeAlgebra μM) V.obj t
        exact (congrArg (c • ·)
          (map_add (RegularTensorContraction.contraction (HeckeAlgebra μM) V.obj) s t)).trans
          (smul_add c _ _)
      map_smul' := fun a t => by
        let _ := NonUnitalModule.regular (HeckeAlgebra μM)
        apply Subtype.ext
        apply NonUnitalModuleHom.ext
        intro c
        exact smul_contraction_smul N μP μM V a c t }

theorem forgetToPseudo_apply
    (t : ((F μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)).obj V).obj)
    (c : HeckeAlgebra μM) :
    (letI := NonUnitalModule.regular (HeckeAlgebra μM)
     show NonUnitalModuleHom (HeckeAlgebra μM) (HeckeAlgebra μM) V.obj from
      ((forgetToPseudo N μP μM V).hom.toAddMonoidHom t).val) c =
      c • RegularTensorContraction.contraction (HeckeAlgebra μM) V.obj t := rfl

/-- The comparison is bijective: injectivity uses the contraction and the
nondegeneracy of `V`; surjectivity uses `T·eK = T * eKM` for a local unit `eK`. -/
theorem forgetToPseudo_bijective :
    Function.Bijective (forgetToPseudo N μP μM V).hom.toAddMonoidHom := by
  let _ := NonUnitalModule.regular (HeckeAlgebra μM)
  let _ := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro t ht
    have hc (c : HeckeAlgebra μM) :
        c • RegularTensorContraction.contraction (HeckeAlgebra μM) V.obj t = 0 :=
      congrArg (fun ψ : ((pseudoF μM μP (QuotientGroup.mk' N)
          (continuous_quotientMk' N)).obj V).obj =>
        (show NonUnitalModuleHom (HeckeAlgebra μM) (HeckeAlgebra μM) V.obj from ψ.val) c) ht
    obtain ⟨e, he⟩ := V.property (RegularTensorContraction.contraction (HeckeAlgebra μM) V.obj t)
    apply RegularTensorContraction.contraction_injective (HeckeAlgebra μM) V.obj
      (isIdempotented μM)
    exact he.symm.trans ((hc _).trans (map_zero _).symm)
  · intro x
    let ψ : NonUnitalModuleHom (HeckeAlgebra μM) (HeckeAlgebra μM) V.obj := x.val
    obtain ⟨e, he⟩ := (RenardHomFunctors.mem_pseudoPart _ _ ψ).mp x.property
    obtain ⟨K, hK, _, _, hfix⟩ :=
      HeckeAlgebra.finiteFamilyLocalUnits P μP {(e : HeckeAlgebra μP)} ⊤
    have heK := (hfix _ (Finset.mem_singleton_self _)).1
    set eM := HeckeAlgebra.normalizedIndicator μM (quotientOpenSubgroup N K)
      (isCompact_quotientOpenSubgroup N K hK)
    have hb (b : HeckeAlgebra μM) : ψ b = b • ψ eM := by
      calc
        ψ b = ψ (op (e : HeckeAlgebra μP) • b) := (he b).symm
        _ = ψ (op (e : HeckeAlgebra μP) •
            op (HeckeAlgebra.normalizedIndicator μP K hK) • b) := by
          rw [← mul_smul, ← op_mul, heK]
        _ = ψ (op (HeckeAlgebra.normalizedIndicator μP K hK) • b) := he _
        _ = ψ (b * eM) := by rw [rightModule_normalizedIndicator]
        _ = b • ψ eM := ψ.map_smul b eM
    obtain ⟨f, hf⟩ := V.property (ψ eM)
    refine ⟨RegularTensorContraction.pure (HeckeAlgebra μM) V.obj (f : HeckeAlgebra μM) (ψ eM),
      ?_⟩
    apply Subtype.ext
    apply NonUnitalModuleHom.ext
    intro c
    change c • ((f : HeckeAlgebra μM) • ψ eM) = ψ c
    rw [hf, hb c]

/-- Naturality of the comparison, from naturality of the contraction. -/
theorem forgetToPseudo_naturality {V W : NondegenerateModuleCat.{uP, v} (HeckeAlgebra μM)}
    (f : V ⟶ W) :
    (F μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)).map f ≫
        forgetToPseudo N μP μM W =
      forgetToPseudo N μP μM V ≫
        (pseudoF μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)).map f := by
  let _ := NonUnitalModule.regular (HeckeAlgebra μM)
  let _ := NonUnitalModule.rightRegular (HeckeAlgebra μM)
  let g : NonUnitalModuleHom (HeckeAlgebra μM) V.obj W.obj := f.hom
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  intro t
  apply Subtype.ext
  apply NonUnitalModuleHom.ext
  intro c
  change c • RegularTensorContraction.contraction (HeckeAlgebra μM) W.obj
      (RegularTensorContraction.tensorMap (HeckeAlgebra μM) g t) =
    g (c • RegularTensorContraction.contraction (HeckeAlgebra μM) V.obj t)
  rw [g.map_smul]
  exact congrArg (c • ·) (DFunLike.congr_fun
    (RegularTensorContraction.contraction_naturality (HeckeAlgebra μM) g) t)

/-- III.2.10: for a normal quotient, pseudo-forgetting is naturally isomorphic
to forgetting. -/
def pseudoFIsoF :
    pseudoF.{uP, uP, v} μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N) ≅
      F.{uP, uP, v} μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N) :=
  (NatIso.ofComponents
    (fun V => nondegenerateIsoOfBijective (forgetToPseudo N μP μM V)
      (forgetToPseudo_bijective N μP μM V))
    (fun f => forgetToPseudo_naturality N μP μM f)).symm

end Pseudo

end Langlands.Hecke.Homomorphism
