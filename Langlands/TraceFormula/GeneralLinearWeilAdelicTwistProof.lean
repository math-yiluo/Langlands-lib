import Langlands.TraceFormula.GeneralLinearWeilAdelicTwistStatement
import Langlands.Global.AdelicGaloisTwistDescent
import Langlands.ClassFieldTheory.Global.IdeleGaloisDescentProof

/-! # The adelic comparison for the Weil restriction of the general linear group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField Opposite
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open Langlands.TraceFormula.AdelicGroupAutomorphism

namespace Langlands.TraceFormula

private local instance (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

private local instance (K : Type u) [Field K] (n : ℕ) :
    Smooth (GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

private def adelicIso (F : Type u) [Field F] [NumberField F]
    {G H : GroupScheme (Spec (CommRingCat.of F))} (e : G ≅ H) :
    AdelicGroupPoints F G ≃ₜ* AdelicGroupPoints F H where
  toFun := map F G H e.hom
  invFun := map F H G e.inv
  left_inv x := by rw [map_comp_apply, e.hom_inv_id, map_id_apply]
  right_inv x := by rw [map_comp_apply, e.inv_hom_id, map_id_apply]
  map_mul' := map_mul (map F G H e.hom)
  continuous_toFun := (map F G H e.hom).continuous
  continuous_invFun := (map F H G e.inv).continuous

private theorem map_mem_rationalSubgroup (F : Type u) [Field F] [NumberField F]
    {G H : GroupScheme (Spec (CommRingCat.of F))} (f : G ⟶ H)
    {x : AdelicGroupPoints F G} (hx : x ∈ rationalSubgroup F G) :
    map F G H f x ∈ rationalSubgroup F H := by
  obtain ⟨q, rfl⟩ := hx
  exact ⟨_, DFunLike.congr_fun (rational_naturality F G f) q⟩

private theorem adelicIso_mem_rationalSubgroup (F : Type u) [Field F] [NumberField F]
    {G H : GroupScheme (Spec (CommRingCat.of F))} (e : G ≅ H) (x : AdelicGroupPoints F G) :
    x ∈ rationalSubgroup F G ↔ adelicIso F e x ∈ rationalSubgroup F H := by
  constructor
  · exact map_mem_rationalSubgroup F e.hom
  · intro hx
    have h := map_mem_rationalSubgroup F e.inv hx
    change (adelicIso F e).symm (adelicIso F e x) ∈ rationalSubgroup F G at h
    rwa [ContinuousMulEquiv.symm_apply_apply] at h

private theorem adelicHomeomorph_mem_rational (F : Type u) [Field F] [NumberField F]
    (n : ℕ) (x : AdelicGroupPoints F (GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) :
    x ∈ rationalSubgroup F _ ↔ GeneralLinearGroupPoints.adelicHomeomorph F n x ∈
      (AdelicGL.rational F n).range := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨_, (GeneralLinearGroupPoints.adelicHomeomorph_rational F n q).symm⟩
  · rintro ⟨m, hm⟩
    obtain ⟨q, rfl⟩ := (GeneralLinearGroupPoints.rationalEquiv F n).surjective m
    exact ⟨q, (GeneralLinearGroupPoints.adelicHomeomorph F n).injective
      ((GeneralLinearGroupPoints.adelicHomeomorph_rational F n q).trans hm)⟩

/-- The base-change isomorphism evaluates each entry on the projected affine point. -/
private theorem baseChange_affine_entry {R S : CommRingCat.{u}} (b : Spec S ⟶ Spec R)
    (n : ℕ) (A : CommAlgCat S)
    (x : (algSpec S).obj (op A) ⟶
      ((GroupScheme.baseChange b).obj (GeneralLinear.groupScheme (Fin n) R)).X) (i j : Fin n) :
    GeneralLinear.affinePointsEquiv (Fin n) S A
        (x ≫ (GeneralLinear.baseChangeIso (Fin n) b).hom.hom.hom) i j =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom
        ((x.left ≫ pullback.fst (GeneralLinear.groupScheme (Fin n) R).X.hom b).appTop
          (GeneralLinear.entrySection (Fin n) R i j)) := by
  rw [GeneralLinear.baseChangeIso, comp_isoOfPoints_hom]
  let T := (algSpec S).obj (op A)
  let y := GeneralLinear.baseChangeGLPointsEquiv (Fin n) b T x
  have h := congrArg (fun g : GL (Fin n) A => g i j)
    (Corepresented.map_affineSectionsIso_pointsEquiv (GeneralLinear.functor (Fin n) S)
      (GeneralLinear.corepresentableBy (Fin n) S) A y)
  change (Corepresented.affineSectionsIso A).hom.hom.toRingHom
    (GeneralLinear.pointsEquiv (Fin n) S T y i j) =
      GeneralLinear.affinePointsEquiv (Fin n) S A y i j at h
  rw [← h, Corepresented.affineSectionsIso_hom_ringHom]
  simp only [y, GeneralLinear.baseChangeGLPointsEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, GeneralLinear.pointsEquiv_apply_apply, baseChangePointsEquiv_left]
  rfl

set_option hygiene false in
local notation "GLK" => GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLL" => GeneralLinear.groupScheme (Fin n) (CommRingCat.of L)

set_option hygiene false in
local notation "BC" => AffineWeil.unitBaseChange K L GLK

set_option hygiene false in
local notation "GLiso" => GeneralLinear.baseChangeIso (Fin n) (Spec.algebraMap K L)

section FieldExtension

variable (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

private theorem ringEquiv_eq_adeleEquiv (σ : L ≃ₐ[K] L) :
    AdeleGalois.ringEquiv K L σ = AdelicFunctoriality.adeleEquiv σ.toRingEquiv := by
  apply RingEquiv.ext
  intro x
  obtain ⟨t, rfl⟩ := (numberFieldAdeleTensorEquiv K L).surjective x
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      rw [AdeleGalois.ringEquiv_tensor, numberFieldAdeleTensorEquiv_tmul,
        numberFieldAdeleTensorEquiv_tmul, map_mul, AdelicFunctoriality.adeleEquiv_diagonal,
        Langlands.ClassFieldTheory.Global.IdeleGaloisDescentProof.adeleEquiv_adeleInclusion]
      rfl
  | add s t hs ht => simp only [map_add, hs, ht]

variable [FiniteDimensional K L]

omit [NumberField K] [FiniteDimensional K L] in
/-- An entry of the upper matrix is the ground coordinate evaluated on the projected point. -/
private theorem baseChange_adelic_entry (n : ℕ) (x : AdelicGroupPoints L BC) (i j : Fin n) :
    GeneralLinearGroupPoints.adelicHomeomorph L n (map L BC GLL (GLiso).hom x) i j =
      (Scheme.ΓSpecIso (CommRingCat.of (Adeles L))).hom
        ((x.left ≫ pullback.fst (GLK).X.hom (Spec.algebraMap K L)).appTop
          (GeneralLinear.entrySection (Fin n) (CommRingCat.of K) i j)) :=
  baseChange_affine_entry (Spec.algebraMap K L) n (CommAlgCat.of (CommRingCat.of L) (Adeles L))
    x i j

private theorem baseChange_adelic_twist (n : ℕ) (σ : L ≃ₐ[K] L) (x : AdelicGroupPoints L BC) :
    GeneralLinearGroupPoints.adelicHomeomorph L n
        (map L BC GLL (GLiso).hom (AdelicGaloisUnit.galoisTwist K L GLK σ x)) =
      AdelicGLTransport.adelicEquiv n σ.toRingEquiv
        (GeneralLinearGroupPoints.adelicHomeomorph L n (map L BC GLL (GLiso).hom x)) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  let f := CommRingCat.ofHom (AdeleGalois.ringEquiv K L σ).toRingHom
  let p : Spec (CommRingCat.of (Adeles L)) ⟶ (GLK).X.left :=
    x.left ≫ pullback.fst (GLK).X.hom (Spec.algebraMap K L)
  have hTwist :
      (AdelicGaloisUnit.galoisTwist K L GLK σ x).left ≫
        pullback.fst (GLK).X.hom (Spec.algebraMap K L) = Spec.map f ≫ p := by
    exact AdelicGaloisUnit.galoisTwist_left_fst K L GLK σ x
  rw [AdelicGLTransport.adelicEquiv_apply, baseChange_adelic_entry, baseChange_adelic_entry,
    hTwist, Scheme.Hom.comp_appTop, ← ringEquiv_eq_adeleEquiv K L σ]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality f) _

end FieldExtension

set_option maxRecDepth 2048 in
/-- The full adelic comparison for Weil-restricted `GL_n` preserves its topology, Galois
 action, and diagonal rational subgroup. -/
theorem generalLinearWeilAdelicTwist : GeneralLinearWeilAdelicTwistStatement.{u} := by
  intro K _ _ L _ _ _ _ n
  dsimp only
  let a := AdelicGaloisUnit.weilAdelicEquiv K L GLK
  let b := adelicIso L GLiso
  let c := GeneralLinearGroupPoints.adelicHomeomorph L n
  refine ⟨⟨(a.trans b).trans c, rfl⟩, ?_, ?_⟩
  · intro σ g
    rw [adelicAut_apply, unitGaloisAut_hom, ← AdelicGaloisUnit.galoisTwist_weilAdelicEquiv]
    exact baseChange_adelic_twist K L n σ (AdelicGaloisUnit.weilAdelicEquiv K L GLK g)
  · intro g
    have hWeil : g ∈ rationalSubgroup K _ ↔ a g ∈ rationalSubgroup L BC := by
      rw [← AdelicWeilRestriction.map_rationalSubgroup K L BC]
      exact (Subgroup.mem_map_iff_mem a.injective).symm
    exact hWeil.trans ((adelicIso_mem_rationalSubgroup L GLiso (a g)).trans
      (adelicHomeomorph_mem_rational L n (b (a g))))

end Langlands.TraceFormula
