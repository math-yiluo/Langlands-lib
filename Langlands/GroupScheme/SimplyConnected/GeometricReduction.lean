import Langlands.GroupScheme.SimplyConnected.FieldExtensionStatement
import Langlands.GroupScheme.CentralIsogeny.BaseChangeStatement
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Reduction of simple-connectedness ascent to geometric inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The geometric ascent step from a field to its algebraic closure. -/
def IsSimplyConnectedAlgebraicClosureAscentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSimplyConnected G →
      IsSimplyConnected ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G)

/-- The extension step when both fields are algebraically closed. -/
def IsSimplyConnectedAlgClosedFieldExtensionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSimplyConnected G →
      IsSimplyConnected
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)

/-- The two geometric inputs used in the field-extension reduction. -/
def SimplyConnectedGeometricInputsStatement : Prop :=
  IsSimplyConnectedAlgebraicClosureAscentStatement.{u} ∧
    IsSimplyConnectedAlgClosedFieldExtensionStatement.{u}

/-- For a semisimple group, simple connectedness is detected by a field extension,
provided semisimplicity and central isogenies are preserved by base change. -/
theorem IsSimplyConnected.of_fieldExtension
    (hsemi : IsSemisimpleFieldExtensionStatement.{u})
    (hcentral : CentralIsogenyBaseChangeStatement.{u})
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSemisimple G)
    (hGK : IsSimplyConnected
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) :
    IsSimplyConnected G := by
  refine ⟨hG, ?_⟩
  intro H f hH hf
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : IsIso ((GroupScheme.baseChange b).map f) :=
    hGK.central_isogeny_isIso _ _ (hsemi k K H hH) (hcentral _ _ b H G f hf)
  obtain ⟨hbSurjective, hbFlat, hbQuasiCompact⟩ := fieldExtension_fpqc k K
  let : Surjective b := hbSurjective
  let : Flat b := hbFlat
  let : QuasiCompact b := hbQuasiCompact
  exact isIso_of_baseChange b f

/-- The two geometric inputs imply arbitrary field-extension ascent, using fpqc
reflection only for morphisms already defined over the field being descended to. -/
theorem isSimplyConnectedFieldExtension_of_geometricInputs
    (hsemi : IsSemisimpleFieldExtensionStatement.{u})
    (hcentral : CentralIsogenyBaseChangeStatement.{u})
    (hgeo : SimplyConnectedGeometricInputsStatement.{u}) :
    IsSimplyConnectedFieldExtensionStatement.{u} := by
  intro k K _ _ _ G hG
  let : Algebra k (AlgebraicClosure K) :=
    ((algebraMap K (AlgebraicClosure K)).comp (algebraMap k K)).toAlgebra
  let ι : AlgebraicClosure k →ₐ[k] AlgebraicClosure K := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) := ι.toRingHom.toAlgebra
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let c := toAlgebraicClosure K
  let a := toAlgebraicClosure k
  let d := Spec.map (CommRingCat.ofHom ι.toRingHom)
  have hcomp : c ≫ b = d ≫ a := by
    dsimp [a, b, c, d, toAlgebraicClosure]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    exact RingHom.ext fun x => (ι.commutes x).symm
  have hbar : IsSimplyConnected
      ((GroupScheme.baseChange d).obj ((GroupScheme.baseChange a).obj G)) :=
    hgeo.2 (AlgebraicClosure k) (AlgebraicClosure K) _ (hgeo.1 k G hG)
  have htotal : IsSimplyConnected ((GroupScheme.baseChange (c ≫ b)).obj G) := by
    rw [hcomp]
    exact hbar.of_iso (baseChangeCompIso a d G)
  have hiter : IsSimplyConnected
      ((GroupScheme.baseChange c).obj ((GroupScheme.baseChange b).obj G)) :=
    htotal.of_iso (baseChangeCompIso b c G).symm
  exact IsSimplyConnected.of_fieldExtension hsemi hcentral (hsemi k K G hG.isSemisimple)
    hiter

end Langlands.GroupScheme
