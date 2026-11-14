import Langlands.AllFieldBZ.Representation.Geometric.ParabolicSupportJacquetStatement
import Langlands.AllFieldBZ.Representation.Parabolic.NormalizedJacquetExactnessProof
import Langlands.Representation.Geometric.ParabolicSupportJacquetProof

/-!
# All-field port of `Langlands.Representation.Geometric.ParabolicSupportJacquetProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ParabolicSupportJacquetProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
open scoped NNReal
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicSupportJacquetComparison geometricPieceFunctor jacquetInductionFunctor padicParabolicSupportJacquetComparison parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor supportCoinvariantsImageHom_injective supportCoinvariantsImageIso supportImageNatIso supportImageQuotientHom supportImageQuotientHom_bijective supportImageQuotientIso supportImageToQuotient supportImageToQuotient_ker supportImageToQuotient_on_support supportImageToQuotient_surjective
universe uF uV

section Algebra
variable {F : Type uF} [CommRing F] {n : ℕ} (C : GeneralLinear.BlockShape n)
  (δ : C.Levi F →* ℝ≥0ˣ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear n F) V)
  (S : Subrepresentation (ρ.comp (C.parabolic F).subtype))

end Algebra
section Padic
variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (C : GeneralLinear.BlockShape n)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
  (S : Subrepresentation (ρ.comp (C.parabolic F.Carrier).subtype))

theorem supportCoinvariantsImageHom_injective :
    letI := T.topology
    IsSmooth ρ → Function.Injective
      (supportCoinvariantsImageHom C (T.leviModulus C) ρ S).hom := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hρ x y hxy
  apply coinvariants_map_injective_of_smooth
    (Parabolic.unipotentFiniteContainment F T C)
    (Jacquet.restrictMap (supportInclusion C ρ S) (C.unipotentRadical F.Carrier))
    Subtype.val_injective (Parabolic.isSmooth_radical F T C ρ hρ)
  exact congrArg Subtype.val hxy

/-- Exactness identifies the support coinvariants with their actual ambient image. -/
def supportCoinvariantsImageIso :
    letI := T.topology
    IsSmooth ρ →
      ((Parabolic.normalizedCoinvariantsFunctor C (T.leviModulus C)).obj
        (Rep.of S.toRepresentation) ≅
          Rep.of (C.normalizedJacquetImage (T.leviModulus C) ρ S).toRepresentation) := by
  letI := T.topology
  intro hρ
  exact Rep.mkIso ((supportCoinvariantsImageHom C (T.leviModulus C) ρ S).hom.ofBijective
    ⟨supportCoinvariantsImageHom_injective T C ρ S hρ,
      supportCoinvariantsImageHom_surjective C (T.leviModulus C) ρ S⟩)

end Padic
section Natural
variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B C : GeneralLinear.BlockShape n)

local notation "Ind" => T.normalizedParabolicInductionFunctor B
local notation "J" => Parabolic.normalizedCoinvariantsFunctor C (T.leviModulus C)

variable (S U : letI := T.topology
  RepSubfunctor (T.normalizedParabolicInductionFunctor B ⋙ SmoothRep.toRep ⋙
    Rep.resFunctor (C.parabolic F.Carrier).subtype))

set_option maxHeartbeats 800000 in
/-- The stepwise coinvariant-to-image comparison is natural in the source representation. -/
def supportImageNatIso :
    letI := T.topology
    S.toFunctor ⋙ J ≅ (parabolicJacquetImageSubfunctor T B C S).toFunctor := by
  letI := T.topology
  exact NatIso.ofComponents
    (fun A => supportCoinvariantsImageIso T C ((Ind).obj A).representation (S.obj A)
      ((Ind).obj A).isSmooth)
    (by
      intro A A' f
      ext q
      obtain ⟨v, rfl⟩ := Jacquet.mk_surjective (S.obj A).toRepresentation _ q
      rfl)

/-- Project the actual upper image to the coinvariants of the support quotient. -/
def supportImageToQuotient :
    letI := T.topology
    (parabolicJacquetImageSubfunctor T B C U).toFunctor ⟶ S.quotientFunctor U ⋙ J := by
  letI := T.topology
  exact (supportImageNatIso T B C U).inv ≫
    Functor.whiskerRight (S.quotientNatProjection U) J

theorem supportImageToQuotient_on_support :
    letI := T.topology
    ∀ A (v : U.representation A),
      ((supportImageToQuotient T B C S U).app A).hom
        ⟨C.jacquetMk ((Ind).obj A).representation v.val, v.val, v.property, rfl⟩ =
      Jacquet.mk (S.quotientObj U A).ρ (C.unipotentRadical F.Carrier)
        ((S.quotientProjection U A).hom v) := by
  let := T.topology
  intro A v
  have h := Rep.inv_hom_apply _ _ ((supportImageNatIso T B C U).app A)
    (Jacquet.mk (U.obj A).toRepresentation (C.unipotentRadical F.Carrier) v)
  exact congrArg (fun q => ((J).map (S.quotientProjection U A)).hom q) h

set_option maxHeartbeats 800000 in
/-- The projection out of the image has precisely the lower image as kernel. -/
theorem supportImageToQuotient_ker :
    letI := T.topology
    (∀ A, S.obj A ≤ U.obj A) → ∀ A,
      LinearMap.ker ((supportImageToQuotient T B C S U).app A).hom.toLinearMap =
        ((parabolicJacquetImageSubfunctor T B C S).lowerInUpper
          (parabolicJacquetImageSubfunctor T B C U) A).toSubmodule := by
  let := T.topology
  intro hSU A
  apply Submodule.ext
  intro x
  change ((supportImageToQuotient T B C S U).app A).hom x = 0 ↔
    x.val ∈ (parabolicJacquetImageSubfunctor T B C S).obj A
  constructor
  · intro hx
    obtain ⟨v, hv, hq⟩ := x.property
    let vU : U.representation A := ⟨v, hv⟩
    have hx' : x = ⟨C.jacquetMk ((Ind).obj A).representation vU.val,
        vU.val, vU.property, rfl⟩ := Subtype.ext hq.symm
    rw [hx', supportImageToQuotient_on_support] at hx
    let L := S.lowerInUpper U A
    let j : L.toRepresentation.IntertwiningMap (U.representation A).ρ :=
      { toLinearMap := L.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
    let q := (S.quotientProjection U A).hom
    have hex : LinearMap.range j.toLinearMap = LinearMap.ker q.toLinearMap := by
      change LinearMap.range L.toSubmodule.subtype = LinearMap.ker L.toSubmodule.mkQ
      rw [Submodule.range_subtype, Submodule.ker_mkQ]
    have he := coinvariants_map_range_eq_ker
      (Jacquet.restrictMap j (C.unipotentRadical F.Carrier))
      (Jacquet.restrictMap q (C.unipotentRadical F.Carrier))
      (S.quotientProjection_surjective U A) hex
    have hm : Jacquet.mk (U.obj A).toRepresentation (C.unipotentRadical F.Carrier) vU ∈
        LinearMap.range (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap j (C.unipotentRadical F.Carrier))) := by
      rw [he]
      exact hx
    obtain ⟨z, hz⟩ := hm
    obtain ⟨z, rfl⟩ := Jacquet.mk_surjective L.toRepresentation
      (C.unipotentRadical F.Carrier) z
    refine ⟨z.val.val, z.property, ?_⟩
    have h := congrArg (supportCoinvariantsMap C ((Ind).obj A).representation (U.obj A)) hz
    exact h.trans hq
  · rintro ⟨v, hv, hq⟩
    let vU : U.representation A := ⟨v, hSU A hv⟩
    have hx' : x = ⟨C.jacquetMk ((Ind).obj A).representation vU.val,
        vU.val, vU.property, rfl⟩ := Subtype.ext hq.symm
    rw [hx', supportImageToQuotient_on_support]
    have hv0 : (S.quotientProjection U A).hom vU = 0 :=
      (Submodule.Quotient.mk_eq_zero (S.lowerInUpper U A).toSubmodule).mpr hv
    rw [hv0, map_zero]
    rfl

/-- Surjectivity follows from the actual quotient map and the upper-image isomorphism. -/
theorem supportImageToQuotient_surjective :
    letI := T.topology
    ∀ A, Function.Surjective ((supportImageToQuotient T B C S U).app A).hom := by
  let := T.topology
  intro A x
  obtain ⟨w, rfl⟩ := Jacquet.mk_surjective (S.quotientObj U A).ρ
    (C.unipotentRadical F.Carrier) x
  obtain ⟨v, rfl⟩ := S.quotientProjection_surjective U A w
  exact ⟨⟨C.jacquetMk ((Ind).obj A).representation v.val, v.val, v.property, rfl⟩,
    supportImageToQuotient_on_support T B C S U A v⟩

set_option maxHeartbeats 3200000 in
/-- Descend the projection to the actual quotient of the two Jacquet images. -/
def supportImageQuotientHom :
    letI := T.topology
    (∀ A, S.obj A ≤ U.obj A) →
      ((parabolicJacquetImageSubfunctor T B C S).quotientFunctor
        (parabolicJacquetImageSubfunctor T B C U) ⟶ S.quotientFunctor U ⋙ J) := by
  letI := T.topology
  intro hSU
  let SI := parabolicJacquetImageSubfunctor T B C S
  let UI := parabolicJacquetImageSubfunctor T B C U
  let α := supportImageToQuotient T B C S U
  exact {
    app A := Rep.ofHom {
      toLinearMap := (SI.lowerInUpper UI A).toSubmodule.liftQ
        (α.app A).hom.toLinearMap
        (supportImageToQuotient_ker T B C S U hSU A).ge
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        obtain ⟨v, rfl⟩ := SI.quotientProjection_surjective UI A x
        exact Rep.hom_comm_apply (α.app A) g v }
    naturality := by
      intro A A' f
      ext x
      obtain ⟨v, rfl⟩ := SI.quotientProjection_surjective UI A x
      exact congrArg (fun k => k.hom v) (α.naturality f) }

theorem supportImageQuotientHom_bijective :
    letI := T.topology
    ∀ (hSU : ∀ A, S.obj A ≤ U.obj A) A,
      Function.Bijective ((supportImageQuotientHom T B C S U hSU).app A).hom := by
  let := T.topology
  intro hSU A
  let SI := parabolicJacquetImageSubfunctor T B C S
  let UI := parabolicJacquetImageSubfunctor T B C U
  constructor
  · apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot _
      ((supportImageToQuotient T B C S U).app A).hom.toLinearMap _
      (supportImageToQuotient_ker T B C S U hSU A).le
  · intro x
    obtain ⟨v, rfl⟩ := supportImageToQuotient_surjective T B C S U A x
    exact ⟨(SI.quotientProjection UI A).hom v, rfl⟩

set_option maxHeartbeats 1600000 in
/-- Exactness gives a natural isomorphism of successive support-image quotients. -/
def supportImageQuotientIso :
    letI := T.topology
    (∀ A, S.obj A ≤ U.obj A) →
      ((parabolicJacquetImageSubfunctor T B C S).quotientFunctor
        (parabolicJacquetImageSubfunctor T B C U) ≅ S.quotientFunctor U ⋙ J) := by
  letI := T.topology
  intro hSU
  exact NatIso.ofComponents
    (fun A => Rep.mkIso
      (((supportImageQuotientHom T B C S U hSU).app A).hom.ofBijective
        (supportImageQuotientHom_bijective T B C S U hSU A)))
    (fun f => (supportImageQuotientHom T B C S U hSU).naturality f)

end Natural
/-- The exact natural comparison for the published fixed support filtration. -/
theorem padicParabolicSupportJacquetComparison :
    PadicParabolicSupportJacquetComparison.{uF, uV} := by
  intro F T n B C
  let := T.topology
  intro m s i
  let t := parabolicInductionSupportFiltration.{uF, uV} T B C s
  exact ⟨supportImageQuotientIso T B C (t.step i.castSucc) (t.step i.succ)
    (fun A => t.step_le_next A i)⟩

end Langlands.AllFieldBZ.Geometric
