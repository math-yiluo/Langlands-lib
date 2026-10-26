import Langlands.Representation.Classification.SimpleEndpointMultiplicityOneStatement
import Langlands.Representation.Category.Abelian
import Langlands.Representation.Filtration.MultiplicityAdditivityProof
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Basic.Complex.Basic

/-!
# A multiplicity-one detector identifies simple endpoints

All counts retain actual finite simple-series witnesses. The aggregate theorem
proves the published focused statement.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory

universe uG uH uV uW uT

/-- A simple subobject and simple quotient detected positively by the same
single-count functor image are isomorphic. -/
theorem simpleEndpointMultiplicityOneCore
    {G : Type uG} [Group G] [TopologicalSpace G]
    {H : Type uH} [Monoid H]
    (F : SmoothRep.{0, uG, uV} ℂ G ⥤ Rep.{uW} ℂ H)
    [F.Additive] [F.PreservesEpimorphisms] [F.PreservesMonomorphisms]
    (A P Q : SmoothRep.{0, uG, uV} ℂ G)
    (hP : P.IsIrreducible) (hQ : Q.IsIrreducible)
    (j : P ⟶ A) (q : A ⟶ Q)
    (hj : Function.Injective (SmoothRep.hom j))
    (hq : Function.Surjective (SmoothRep.hom q))
    (τ : Rep.{uT} ℂ H) (mP mQ : ℕ)
    (hA : HasJordanHolderMultiplicity (F.obj A) τ 1)
    (hFP : HasJordanHolderMultiplicity (F.obj P) τ mP)
    (hFQ : HasJordanHolderMultiplicity (F.obj Q) τ mQ)
    (hmP : 0 < mP) (hmQ : 0 < mQ) :
    Nonempty (P ≅ Q) := by
  let f := (SmoothRep.hom q).comp (SmoothRep.hom j)
  by_cases hf : f = 0
  · have hzero : j ≫ q = 0 :=
      congrArg (fun l : P.representation.IntertwiningMap Q.representation =>
        SmoothRep.ofHom l) hf
    have hFzero : F.map j ≫ F.map q = 0 := by
      rw [← F.map_comp, hzero, F.map_zero]
    let : Mono j := (SmoothRep.mono_iff_injective j).mpr hj
    let : Epi q := (SmoothRep.epi_iff_surjective q).mpr hq
    let d := (F.map j).hom
    let r := (F.map q).hom
    have hd : Function.Injective d :=
      (Rep.mono_iff_injective (F.map j)).mp inferInstance
    have hr : Function.Surjective r :=
      (Rep.epi_iff_surjective (F.map q)).mp inferInstance
    have hdr (x : (F.obj P).V) : r (d x) = 0 :=
      congrArg (fun l : F.obj P ⟶ F.obj Q => l.hom x) hFzero
    let K : Rep.{uW} ℂ H := Rep.of r.ker.toRepresentation
    let i : K.ρ.IntertwiningMap (F.obj A).ρ :=
      { toLinearMap := r.ker.toSubmodule.subtype
        isIntertwining' _ := rfl }
    have hex : LinearMap.range i.toLinearMap = LinearMap.ker r.toLinearMap :=
      Submodule.range_subtype _
    obtain ⟨mK, mQ', hK, hQ', hsum⟩ :=
      jordanHolderShortExactDecomposition ℂ H K (F.obj A) (F.obj Q) τ i r
        (Submodule.injective_subtype _) hr hex 1 hA
    let k : (F.obj P).ρ.IntertwiningMap K.ρ :=
      { toLinearMap := d.toLinearMap.codRestrict r.ker.toSubmodule hdr
        isIntertwining' g := by
          ext x
          exact congrArg (fun l : (F.obj P).V →ₗ[ℂ] (F.obj A).V => l x)
            (d.isIntertwining' g) }
    have hk : Function.Injective k :=
      fun a b h => hd (congrArg Subtype.val h)
    have hle := jordanHolderInjectiveMonotonicity ℂ H (F.obj P) K τ k hk
      mP mK hFP hK
    have heq := HasJordanHolderMultiplicity.unique hQ' hFQ
    omega
  · let : Representation.IsIrreducible P.representation := hP
    let : Representation.IsIrreducible Q.representation := hQ
    have hbij := (Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf
    exact ⟨SmoothRep.mkIso (f.ofBijective hbij)⟩

/-- The exact simple-endpoint identification statement. -/
theorem simpleEndpointMultiplicityOne :
    SimpleEndpointMultiplicityOneStatement.{uG, uH, uV, uW, uT} := by
  intro G _ _ H _ F _ _ _ A P Q hP hQ j q hj hq τ mP mQ hA hFP hFQ hmP hmQ
  exact simpleEndpointMultiplicityOneCore F A P Q hP hQ j q hj hq τ mP mQ
    hA hFP hFQ hmP hmQ

end Langlands.Classification
