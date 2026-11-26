import Langlands.Global.InfiniteAdelicMaximalCompactConjugacy
import Langlands.Global.InfinitePlaceLeviIwasawaProof
import Langlands.GroupScheme.Absolute.SolvableUnipotentFactorizationOfQuotient
import Langlands.GroupScheme.Rational.LeviMultiplication

/-! # Maximal compact subgroups of an archimedean Levi under radical conjugation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme InfiniteAdelicGroupPoints CompactIwasawa

private theorem isMaximalCompact_pi {I : Type*} {X : I → Type*}
    [∀ i, Group (X i)] [∀ i, TopologicalSpace (X i)] (D : ∀ i, Subgroup (X i))
    (hD : ∀ i, IsMaximalCompact (D i)) : IsMaximalCompact (Subgroup.pi Set.univ D) := by
  classical
  refine ⟨isCompact_univ_pi (fun i => (hD i).1), fun L hL hle => ?_⟩
  refine le_antisymm (fun x hx => (Subgroup.mem_pi Set.univ).mpr fun i _ => ?_) hle
  let p := Pi.evalMonoidHom X i
  have hcompact : IsCompact (L.map p : Set (X i)) := hL.image (continuous_apply i)
  have hsub : D i ≤ L.map p := by
    intro a ha
    let y := Function.update (1 : ∀ j, X j) i a
    have hy : y ∈ Subgroup.pi Set.univ D := (Subgroup.mem_pi Set.univ).mpr fun j _ => by
      by_cases hj : j = i
      · subst j
        simpa only [y, Function.update_self] using ha
      · simpa only [y, Function.update_of_ne hj, Pi.one_apply] using (D j).one_mem
    exact ⟨y, hle hy, Function.update_self i a 1⟩
  exact (hD i).2 (L.map p) hcompact hsub ▸ (show p x ∈ L.map p from ⟨x, hx, rfl⟩)

variable {F : Type u} [Field F] [NumberField F]
  {G Q M V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine Q.X.left] [IsAffine M.X.left]
  (q : Q ⟶ G) (iV : V ⟶ Q) (l : M ⟶ Q)

omit [NumberField F] in
private theorem atPlace_target {H J : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] [IsAffine J.X.left] (j : H ⟶ J) (w : NumberField.InfinitePlace F)
    (x : InfiniteAdelicGroupPoints F H) :
    atPlace F J w (H.affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F)) x) =
      H.affinePointsTarget j (CommAlgCat.of F w.Completion) (atPlace F H w x) :=
  DFunLike.congr_fun (H.affinePointsTarget_naturality j
    (CommAlgCat.ofHom (Pi.evalAlgHom F (fun v : NumberField.InfinitePlace F => v.Completion) w))) x

private theorem exists_levi_compatible_compact (hG : IsConnectedReductive G)
    (hq : IsParabolicSubgroup q) (hl : IsRationalLeviSubgroup l) :
    ∃ D : Subgroup (InfiniteAdelicGroupPoints F G),
      IsMaximalCompact D ∧
      IsMaximalCompact (D.comap (M.affinePointsTarget (l ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F)))) ∧
      ∀ x : InfiniteAdelicGroupPoints F G,
        ∃ (y : InfiniteAdelicGroupPoints F Q) (d : D),
          Q.affinePointsTarget q (CommAlgCat.of F (InfiniteAdeleRing F)) y * d.val = x := by
  classical
  choose Dv hDv using fun v =>
    InfinitePlaceGroupPoints.leviCompatibleIwasawaStatement F G hG Q q hq M l hl v
  let D := (Subgroup.pi Set.univ Dv).comap (completions F G).toMonoidHom
  let Hv (v : NumberField.InfinitePlace F) :=
    (Dv v).comap (M.affinePointsTarget (l ≫ q) (CommAlgCat.of F v.Completion))
  have hH : D.comap (M.affinePointsTarget (l ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F))) =
      (Subgroup.pi Set.univ Hv).comap (completions F M).toMonoidHom := by
    ext x
    change (∀ v, v ∈ (Set.univ : Set (NumberField.InfinitePlace F)) →
        atPlace F G v (M.affinePointsTarget (l ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F)) x) ∈ Dv v) ↔
      ∀ v, v ∈ (Set.univ : Set (NumberField.InfinitePlace F)) →
        M.affinePointsTarget (l ≫ q) (CommAlgCat.of F v.Completion) (atPlace F M v x) ∈ Dv v
    simp only [atPlace_target]
  refine ⟨D, (isMaximalCompact_comap_equiv (completions F G)).mpr
    (isMaximalCompact_pi Dv (fun v => (hDv v).1)), hH.symm ▸
    (isMaximalCompact_comap_equiv (completions F M)).mpr
      (isMaximalCompact_pi Hv (fun v => (hDv v).2.2.2)), fun x => ?_⟩
  have hfact (v : NumberField.InfinitePlace F) :
      ∃ (y : InfinitePlaceGroupPoints F Q v) (d : InfinitePlaceGroupPoints F G v),
        d ∈ Dv v ∧ Q.affinePointsTarget q (CommAlgCat.of F v.Completion) y * d = atPlace F G v x := by
    have hx : atPlace F G v x ∈ Set.range (Q.affinePointsTarget q (CommAlgCat.of F v.Completion)) *
        (Dv v : Set (InfinitePlaceGroupPoints F G v)) := by
      rw [(hDv v).2.1]
      exact Set.mem_univ _
    obtain ⟨_, ⟨y, rfl⟩, d, hd, h⟩ := hx
    exact ⟨y, d, hd, h⟩
  choose y d hd he using hfact
  refine ⟨assemble F Q y, ⟨assemble F G d, ?_⟩, ?_⟩
  · change completions F G (assemble F G d) ∈ Subgroup.pi Set.univ Dv
    exact (Subgroup.mem_pi Set.univ).mpr fun v _ => by
      simpa only [completions_apply, atPlace_assemble] using hd v
  · apply (completions F G).injective
    funext v
    change atPlace F G v (_ * assemble F G d) = atPlace F G v x
    rw [map_mul, atPlace_target, atPlace_assemble, atPlace_assemble]
    exact he v

omit [NumberField F] [IsAffine G.X.left] [IsAffine Q.X.left] [IsAffine M.X.left] in
private theorem factor_infinite_parabolic [IsIso (subgroupMultiplication l iV)]
    (x : InfiniteAdelicGroupPoints F Q) :
    ∃ (v : InfiniteAdelicGroupPoints F V) (m : InfiniteAdelicGroupPoints F M),
      V.affinePointsTarget (iV ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F)) v *
        M.affinePointsTarget (l ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F)) m =
      Q.affinePointsTarget q (CommAlgCat.of F (InfiniteAdeleRing F)) x := by
  let : IsIso (subgroupMultiplication iV l) :=
    (isIso_subgroupMultiplication_reverse_iff l iV).mp inferInstance
  obtain ⟨v, m, h⟩ := exists_factorization_of_isIso_subgroupMultiplication iV l x
  refine ⟨v, m, ?_⟩
  have he := congrArg (Q.affinePointsTarget q (CommAlgCat.of F (InfiniteAdeleRing F))) h
  simpa only [map_mul, affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc] using he

/-- For any ambient maximal infinite compact, one radical point conjugates the image of
some maximal infinite Levi compact into it. -/
theorem exists_leviCompact_conj_by_radical [IsIso (subgroupMultiplication l iV)]
    (hG : IsConnectedReductive G) (hq : IsParabolicSubgroup q) (hl : IsRationalLeviSubgroup l)
    (K : Subgroup (InfiniteAdelicGroupPoints F G)) (hK : IsMaximalCompact K) :
    ∃ H : Subgroup (InfiniteAdelicGroupPoints F M), IsMaximalCompact H ∧
      ∃ v : InfiniteAdelicGroupPoints F V, ∀ m ∈ H,
        let u := V.affinePointsTarget (iV ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F)) v
        u * M.affinePointsTarget (l ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F)) m * u⁻¹ ∈ K := by
  obtain ⟨D, hD, hH, hcov⟩ := exists_levi_compatible_compact q l hG hq hl
  obtain ⟨t, ht⟩ := infiniteAdelicMaximalCompactConjugacy F G D K hG hD hK
  obtain ⟨y, d, hd⟩ := hcov t
  obtain ⟨v, m₀, hv⟩ := factor_infinite_parabolic q iV l y
  let A := CommAlgCat.of F (InfiniteAdeleRing F)
  let j := M.affinePointsTarget (l ≫ q) A
  let u := V.affinePointsTarget (iV ≫ q) A v
  let H₀ := D.comap j
  let c : InfiniteAdelicGroupPoints F M ≃ₜ* InfiniteAdelicGroupPoints F M :=
    { toMulEquiv := MulAut.conj m₀
      continuous_toFun := IsTopologicalGroup.continuous_conj m₀
      continuous_invFun := by
        change Continuous fun x : InfiniteAdelicGroupPoints F M => m₀⁻¹ * x * m₀
        exact (continuous_const.mul continuous_id).mul continuous_const }
  refine ⟨H₀.map c.toMonoidHom, hH.map c, v, ?_⟩
  rintro _ ⟨m, hm, rfl⟩
  have hmD : j m ∈ D := hm
  have hx : d.val⁻¹ * j m * d.val ∈ D := D.mul_mem (D.mul_mem (D.inv_mem d.property) hmD) d.property
  rw [← ht]
  refine ⟨_, hx, ?_⟩
  change t * (d.val⁻¹ * j m * d.val) * t⁻¹ = u * j (m₀ * m * m₀⁻¹) * u⁻¹
  rw [← hd, ← hv]
  change (u * j m₀ * d.val) * (d.val⁻¹ * j m * d.val) * (u * j m₀ * d.val)⁻¹ =
    u * j (m₀ * m * m₀⁻¹) * u⁻¹
  simp only [map_mul, map_inv]
  group

end Langlands.Automorphic.GroupSchemeFunctions
