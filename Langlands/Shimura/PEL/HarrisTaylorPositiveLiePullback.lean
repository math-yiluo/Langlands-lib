import Langlands.AlgebraicGeometry.ImaginaryQuadraticEigensheafPullback
import Langlands.AlgebraicGeometry.PullbackFiniteLocalBasisRankProof
import Langlands.AbelianScheme.LieBaseChangeNaturalityProof
import Langlands.AbelianScheme.LieRationalBaseChange
import Langlands.Shimura.PEL.HarrisTaylorLieCompatibility
import Langlands.Shimura.PEL.ReflexSectionPullback

/-! # Actual positive Lie pullback for Harris--Taylor -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField Algebra
open Langlands.AbelianScheme Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.HarrisTaylor

variable {K : Type} [Field K]
  {S T : AlgebraicGeometry.Scheme.{0}}
  (s : S ⟶ Spec (CommRingCat.of K)) (b : T ⟶ S)

/-- Structural scalars on global sections pull back by the actual scheme morphism. -/
theorem structureSection_pullback_top (a : K) :
    b.appTop (secHom s ⊤ a) = secHom (b ≫ s) ⊤ a := by
  have h := secHom_comp_appLE s b ⊤ ⊤ (by simp)
  have hb : b.appLE ⊤ ⊤ (by simp) = b.appTop := by
    simp [Scheme.Hom.appLE]
  rw [hb] at h
  exact ConcreteCategory.congr_hom h a

variable [NumberField K]

/-- The global coefficient map is the actual structural K-algebra pullback map. -/
def structureSectionPullbackAlgHom :
    letI : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
    letI : Algebra K Γ(T, ⊤) := (secHom (b ≫ s) ⊤).hom.toAlgebra
    Γ(S, ⊤) →ₐ[K] Γ(T, ⊤) := by
  letI : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
  letI : Algebra K Γ(T, ⊤) := (secHom (b ≫ s) ⊤).hom.toAlgebra
  exact { b.appTop.hom with commutes' := structureSection_pullback_top s b }

variable (L : Type) [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L K]
  {A : Type} [Ring A] [Algebra ℚ A] [Algebra K A]
  (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)

omit [NumberField L] [IsCMField L] [IsQuadraticExtension ℚ L] in
/-- The canonical actual Lie comparison intertwines every imaginary-field element. -/
theorem imaginaryLieAction_pullback (r : L) :
    (AlgebraicGeometry.Scheme.Modules.pullback b).map (imaginaryLieAction L s B i r) ≫
        (lieBaseChangeIso b B).hom =
      (lieBaseChangeIso b B).hom ≫
        imaginaryLieAction L (b ≫ s) ((baseChange b).obj B)
          ((rationalBaseChangeEnd b B).comp i) r := by
  exact lieRationalOrderAction_baseChange_of_naturality s b
    (lieBaseChangeNaturalityStatements S).1 B i.toRingHom
      (algebraMap K A (algebraMap L K r))

/-- The actual full natural or conjugate central Lie eigensheaf commutes with pullback. -/
def lieEigensheafPullbackIso (conjugate : Bool) :
    (AlgebraicGeometry.Scheme.Modules.pullback b).obj (lieEigensheaf L s B i conjugate) ≅
      lieEigensheaf L (b ≫ s) ((baseChange b).obj B)
        ((rationalBaseChangeEnd b B).comp i) conjugate := by
  letI : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
  letI : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
  letI : IsScalarTower ℚ K Γ(S, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra K Γ(T, ⊤) := (secHom (b ≫ s) ⊤).hom.toAlgebra
  letI : Algebra ℚ Γ(T, ⊤) := Algebra.compHom Γ(T, ⊤) (algebraMap ℚ K)
  letI : IsScalarTower ℚ K Γ(T, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  simpa only [lieEigensheaf, sheafFactorCharacter_eq_imaginaryLieCharacter L s,
    sheafFactorCharacter_eq_imaginaryLieCharacter L (b ≫ s)] using
    sheafEigenPullbackIso L K b (structureSectionPullbackAlgHom s b) rfl
      (imaginaryLieAction L s B i)
      (imaginaryLieAction L (b ≫ s) ((baseChange b).obj B)
        ((rationalBaseChangeEnd b B).comp i))
      (lieBaseChangeIso b B) (imaginaryLieAction_pullback s b L B i) conjugate

/-- The constructed comparison is the pulled-back inclusion followed by the actual
canonical Lie comparison and target eigenprojection. -/
theorem lieEigensheafPullbackIso_hom (conjugate : Bool) :
    (lieEigensheafPullbackIso s b L B i conjugate).hom =
      (AlgebraicGeometry.Scheme.Modules.pullback b).map (lieEigensheafι L s B i conjugate) ≫
        (lieBaseChangeIso b B).hom ≫
          lieEigenProjection L (b ≫ s) ((baseChange b).obj B)
            ((rationalBaseChangeEnd b B).comp i) conjugate := by
  cases conjugate <;> rfl

/-- The actual eigensheaf pullback comparison intertwines the full rational algebra action. -/
theorem lieEigensheafPullbackIso_intertwines (conjugate : Bool) (a : A) :
    (AlgebraicGeometry.Scheme.Modules.pullback b).map (lieEigensheafAction L s B i conjugate a) ≫
        (lieEigensheafPullbackIso s b L B i conjugate).hom =
      (lieEigensheafPullbackIso s b L B i conjugate).hom ≫
        lieEigensheafAction L (b ≫ s) ((baseChange b).obj B)
          ((rationalBaseChangeEnd b B).comp i) conjugate a := by
  let : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
  let : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
  let : IsScalarTower ℚ K Γ(S, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra K Γ(T, ⊤) := (secHom (b ≫ s) ⊤).hom.toAlgebra
  let : Algebra ℚ Γ(T, ⊤) := Algebra.compHom Γ(T, ⊤) (algebraMap ℚ K)
  let : IsScalarTower ℚ K Γ(T, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  cases conjugate
  · exact sheafEigenPullbackMap_intertwines L K b (structureSectionPullbackAlgHom s b) rfl
      (imaginaryLieAction L s B i)
      (imaginaryLieAction L (b ≫ s) ((baseChange b).obj B) ((rationalBaseChangeEnd b B).comp i))
      (lieBaseChangeIso b B).hom (imaginaryLieAction_pullback s b L B i)
      (lieRationalOrderAction s B i.toRingHom)
      (lieRationalOrderAction (b ≫ s) ((baseChange b).obj B)
        ((rationalBaseChangeEnd b B).comp i).toRingHom)
      (imaginaryLieAction_commutes L s B i)
      (imaginaryLieAction_commutes L (b ≫ s) ((baseChange b).obj B)
        ((rationalBaseChangeEnd b B).comp i))
      (lieRationalOrderAction_baseChange_of_naturality s b
        (lieBaseChangeNaturalityStatements S).1 B i.toRingHom) false a
  · exact sheafEigenPullbackMap_intertwines L K b (structureSectionPullbackAlgHom s b) rfl
      (imaginaryLieAction L s B i)
      (imaginaryLieAction L (b ≫ s) ((baseChange b).obj B) ((rationalBaseChangeEnd b B).comp i))
      (lieBaseChangeIso b B).hom (imaginaryLieAction_pullback s b L B i)
      (lieRationalOrderAction s B i.toRingHom)
      (lieRationalOrderAction (b ≫ s) ((baseChange b).obj B)
        ((rationalBaseChangeEnd b B).comp i).toRingHom)
      (imaginaryLieAction_commutes L s B i)
      (imaginaryLieAction_commutes L (b ≫ s) ((baseChange b).obj B)
        ((rationalBaseChangeEnd b B).comp i))
      (lieRationalOrderAction_baseChange_of_naturality s b
        (lieBaseChangeNaturalityStatements S).1 B i.toRingHom) true a

/-- The actual original-order natural and conjugate Lie tensor factors commute with pullback. -/
def lieTensorPullbackIso (conjugate : Bool) :
    (AlgebraicGeometry.Scheme.Modules.pullback b).obj (lieTensorSheaf L s B i conjugate) ≅
      lieTensorSheaf L (b ≫ s) ((baseChange b).obj B)
        ((rationalBaseChangeEnd b B).comp i) conjugate :=
  (AlgebraicGeometry.Scheme.Modules.pullback b).mapIso (lieTensorSheafIso L s B i conjugate) ≪≫
    lieEigensheafPullbackIso s b L B i conjugate ≪≫
      (lieTensorSheafIso L (b ≫ s) ((baseChange b).obj B)
        ((rationalBaseChangeEnd b B).comp i) conjugate).symm

/-- The original-order tensor comparison intertwines the full rational algebra action. -/
theorem lieTensorPullbackIso_intertwines (conjugate : Bool) (a : A) :
    (AlgebraicGeometry.Scheme.Modules.pullback b).map (lieTensorAction L s B i conjugate a) ≫
        (lieTensorPullbackIso s b L B i conjugate).hom =
      (lieTensorPullbackIso s b L B i conjugate).hom ≫
        lieTensorAction L (b ≫ s) ((baseChange b).obj B)
          ((rationalBaseChangeEnd b B).comp i) conjugate a := by
  apply (cancel_mono (lieTensorSheafIso L (b ≫ s) ((baseChange b).obj B)
    ((rationalBaseChangeEnd b B).comp i) conjugate).hom).mp
  simp only [lieTensorPullbackIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    lieTensorAction_comparison]
  rw [← Functor.map_comp_assoc, lieTensorAction_comparison, Functor.map_comp]
  simp only [Category.assoc]
  rw [lieEigensheafPullbackIso_intertwines]
  simp

private theorem eq_scalar_pullback_of_iso {M : S.Modules} {N : T.Modules}
    (e : (AlgebraicGeometry.Scheme.Modules.pullback b).obj M ≅ N)
    (α : End M) (β : End N)
    (he : (AlgebraicGeometry.Scheme.Modules.pullback b).map α ≫ e.hom = e.hom ≫ β)
    (r : Γ(S, ⊤)) (hα : α = scalarHom r (𝟙 M)) :
    β = scalarHom (b.appTop r) (𝟙 N) := by
  apply (cancel_epi e.hom).mp
  rw [← he, hα]
  change (AlgebraicGeometry.Scheme.Modules.pullback b).map (r • (𝟙 M : M ⟶ M)) ≫ e.hom =
    e.hom ≫ (b.appTop r • (𝟙 N : N ⟶ N))
  rw [pullback_map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp, Linear.comp_smul,
    Category.id_comp, Category.comp_id]

variable (E : Type) [Field E] [Algebra E K]

/-- The two positive central actions remain equal after arbitrary scheme pullback. -/
theorem positiveLieScalarCondition_pullback
    (h : PositiveLieScalarCondition L E s B i) :
    PositiveLieScalarCondition L E (b ≫ s) ((baseChange b).obj B)
      ((rationalBaseChangeEnd b B).comp i) := by
  intro a
  rw [← structureSection_pullback_top s b]
  exact eq_scalar_pullback_of_iso b (lieTensorPullbackIso s b L B i false) _ _
    (lieTensorPullbackIso_intertwines s b L B i false
      (algebraMap K A (algebraMap E K a))) _ (h a)

/-- The full source positive rank and scalar condition is preserved by arbitrary pullback. -/
theorem lieCompatibility_pullback (n : ℕ) (h : LieCompatibility L E s B i n) :
    LieCompatibility L E (b ≫ s) ((baseChange b).obj B)
      ((rationalBaseChangeEnd b B).comp i) n := by
  refine ⟨?_, positiveLieScalarCondition_pullback s b L B i E h.2⟩
  exact ((pullbackFiniteLocalBasisRank T S b (lieTensorSheaf L s B i false)).2 n h.1).ofIso
    (lieTensorPullbackIso s b L B i false)

/-- The equivalent full eigensheaf formulation is also preserved by arbitrary pullback. -/
theorem eigenLieCompatibility_pullback (n : ℕ) (h : EigenLieCompatibility L E s B i n) :
    EigenLieCompatibility L E (b ≫ s) ((baseChange b).obj B)
      ((rationalBaseChangeEnd b B).comp i) n := by
  exact (lieCompatibility_iff_eigensheaf L E (b ≫ s) ((baseChange b).obj B)
    ((rationalBaseChangeEnd b B).comp i) n).mp
      (lieCompatibility_pullback s b L B i E n
        ((lieCompatibility_iff_eigensheaf L E s B i n).mpr h))

end Langlands.Shimura.HarrisTaylor
