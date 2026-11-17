import Langlands.GroupScheme.Torus.AffineDiagonalizableInfinitesimalCentrality
import Langlands.GroupScheme.CentralIsogeny.FpqcReflectionHelpers
import Mathlib.AlgebraicGeometry.Cover.Sigma

/-! # Nilpotent centrality with a multiplicative-type source and affine target -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem hom_ext_flatCover {X Y : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Flat) X)
    (f g : X ⟶ Y) (h : ∀ j, 𝒰.f j ≫ f = 𝒰.f j ≫ g) : f = g := by
  let p : ∐ 𝒰.X ⟶ X := Sigma.desc 𝒰.f
  have : Flat p := IsZariskiLocalAtSource.sigmaDesc 𝒰.map_prop
  have : Surjective p := by
    constructor
    intro x
    obtain ⟨j, y, rfl⟩ := 𝒰.exists_eq x
    exact ⟨Sigma.ι 𝒰.X j y, by rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]⟩
  have : Epi p := Flat.epi_of_flat_of_surjective p
  apply (cancel_epi p).mp
  apply Sigma.hom_ext
  intro j
  simpa only [p, ← Category.assoc, Sigma.ι_comp_desc] using h j

/-- A jointly surjective flat family detects actual centrality. -/
theorem IsCentral.of_flatCover {S : Scheme.{u}} {H G : GroupScheme S} {i : H ⟶ G}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Flat) S)
    (hc : ∀ j, IsCentral ((GroupScheme.baseChange (𝒰.f j)).map i)) :
    IsCentral i := by
  intro T x
  apply mem_center.mpr
  intro T' a y
  change (a ≫ (x ≫ i.hom.hom)) * y = y * (a ≫ (x ≫ i.hom.hom))
  apply Over.OverMorphism.ext
  apply hom_ext_flatCover (𝒰.pullback₁ T'.hom)
  intro j
  let V : Over (𝒰.X j) := (Over.pullback (𝒰.f j)).obj T'
  let q : (Over.map (𝒰.f j)).obj V ⟶ T' :=
    Over.homMk (pullback.fst T'.hom (𝒰.f j)) pullback.condition
  let x' := (baseChangePointsEquiv (𝒰.f j) H V).symm (q ≫ a ≫ x)
  let y' := (baseChangePointsEquiv (𝒰.f j) G V).symm (q ≫ y)
  have he := congrArg (baseChangePointsEquiv (𝒰.f j) G V)
    (commute_of_mem_center (hc j V x') y').eq
  have hq : q ≫ ((a ≫ (x ≫ i.hom.hom)) * y) =
      q ≫ (y * (a ≫ (x ≫ i.hom.hom))) := by
    simpa only [map_mul, baseChangePointsEquiv_comp, x', y',
      MulEquiv.apply_symm_apply, MonObj.comp_mul, Category.assoc] using he
  exact congrArg (fun z => z.left) hq

namespace MultiplicativeTypeAffineInfinitesimalCentrality

variable {S S' S'' : Scheme.{u}} {H G : GroupScheme S}

/-- Centrality is unchanged by the canonical comparison between direct and
successive base changes. -/
theorem isCentral_baseChange_comp_iff (b : S' ⟶ S) (c : S'' ⟶ S') (i : H ⟶ G) :
    IsCentral ((GroupScheme.baseChange (c ≫ b)).map i) ↔
      IsCentral ((GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map i)) := by
  let eH := Descent.pullbackComparison b c (c ≫ b) rfl H
  let eG := Descent.pullbackComparison b c (c ≫ b) rfl G
  have he : (GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map i) ≫ eG.hom =
      eH.hom ≫ (GroupScheme.baseChange (c ≫ b)).map i :=
    Descent.pullbackComparison_naturality b c (c ≫ b) rfl i
  constructor
  · intro hc
    have h := (hc.comp eH.hom).comp_iso eG.symm
    simpa only [← he, Category.assoc, Iso.symm_hom, Iso.hom_inv_id,
      Category.comp_id] using h
  · intro hc
    have h := (hc.comp_iso eG).comp eH.inv
    simpa only [he, Iso.inv_hom_id_assoc] using h

/-- A commuting base square carries centrality to the iterated pullback. -/
theorem isCentral_baseChange_of_commSq {T : Scheme.{u}}
    (b : S' ⟶ S) (c : S'' ⟶ S') (d : T ⟶ S) (e : S'' ⟶ T)
    (h : c ≫ b = e ≫ d) (i : H ⟶ G)
    (hc : IsCentral ((GroupScheme.baseChange d).map i)) :
    IsCentral ((GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map i)) := by
  apply (isCentral_baseChange_comp_iff b c i).mp
  rw [h]
  exact (isCentral_baseChange_comp_iff d e i).mpr (hc.baseChange e)

variable {R B : CommRingCat.{u}} [Algebra R B]

/-- Quotient centrality persists over any algebra, using the extended ideal. -/
theorem isCentral_quotient_baseChange
    {H G : GroupScheme (Spec R)} (i : H ⟶ G) (I : Ideal R)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map i)) :
    IsCentral ((GroupScheme.baseChange
      (Spec.algebraMap B (B ⧸ I.map (algebraMap R B)))).map
        ((GroupScheme.baseChange (Spec.algebraMap R B)).map i)) := by
  let J := I.map (algebraMap R B)
  let f : R ⧸ I →+* B ⧸ J :=
    Ideal.quotientMap J (algebraMap R B) Ideal.le_comap_map
  apply isCentral_baseChange_of_commSq
    (Spec.algebraMap R B) (Spec.algebraMap B (B ⧸ J))
    (Spec.algebraMap R (R ⧸ I)) (Spec.map (CommRingCat.ofHom f)) _ i hc
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B)) =
    Spec.map (CommRingCat.ofHom f) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- Nilpotence of an ideal is preserved by scalar extension. -/
theorem isNilpotent_map (I : Ideal R) (hI : IsNilpotent I) :
    IsNilpotent (I.map (algebraMap R B)) := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  rw [← Ideal.map_pow, hn]
  exact Ideal.map_bot

/-- Centrality can be lifted on a diagonalizable affine algebra chart. -/
theorem isCentral_baseChange_of_isDiagonalizable
    {H G : GroupScheme (Spec R)} [IsAffine G.X.left]
    (i : H ⟶ G)
    (hH : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap R B)).obj H))
    (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map i)) :
    IsCentral ((GroupScheme.baseChange (Spec.algebraMap R B)).map i) := by
  have : IsAffine ((GroupScheme.baseChange (Spec.algebraMap R B)).obj G).X.left := by
    change IsAffine (pullback G.X.hom (Spec.algebraMap R B))
    infer_instance
  exact AffineDiagonalizableInfinitesimalCentrality.isCentral_of_isDiagonalizable hH
    ((GroupScheme.baseChange (Spec.algebraMap R B)).map i)
    (I.map (algebraMap R B)) (isNilpotent_map I hI)
    (isCentral_quotient_baseChange i I hc)

omit [Algebra R B] in
/-- The affine chart need not come with a specified algebra structure. -/
theorem isCentral_affineChart_of_isDiagonalizable
    {H G : GroupScheme (Spec R)} [IsAffine G.X.left]
    (b : Spec B ⟶ Spec R) (i : H ⟶ G)
    (hH : RelativeMultiplicativeType.IsDiagonalizable ((GroupScheme.baseChange b).obj H))
    (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map i)) :
    IsCentral ((GroupScheme.baseChange b).map i) := by
  let : Algebra R B := (Spec.preimage b).hom.toAlgebra
  have hb : Spec.algebraMap R B = b := Spec.map_preimage b
  rw [← hb] at hH ⊢
  exact isCentral_baseChange_of_isDiagonalizable i hH I hI hc

/-- For a multiplicative-type source and affine target, centrality lifts across
any nilpotent quotient of the affine base. -/
theorem isCentral_of_isMultiplicativeType
    {H G : GroupScheme (Spec R)} [IsAffine G.X.left]
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H) (i : H ⟶ G)
    (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map i)) :
    IsCentral i := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  apply IsCentral.of_flatCover (𝒰.changeProp (Q := @Flat) fun j => (𝒰.map_prop j).1)
  intro j
  let 𝒱 := (𝒰.X j).affineOpenCover
  apply IsCentral.of_flatCover (𝒱.openCover.changeProp (Q := @Flat) fun _ => inferInstance)
  intro k
  apply (isCentral_baseChange_comp_iff (𝒰.f j) (𝒱.f k) i).mp
  apply isCentral_affineChart_of_isDiagonalizable (𝒱.f k ≫ 𝒰.f j) i _ I hI hc
  exact RelativeMultiplicativeType.IsDiagonalizable.of_iso
    (Descent.pullbackComparison (𝒰.f j) (𝒱.f k) (𝒱.f k ≫ 𝒰.f j) rfl H).symm
    ((h𝒰 j).baseChange (𝒱.f k))

/-- The original monomorphic source, with commutativity obtained from the lifted
centrality. -/
def commGroupSchemeOfNilpotentQuotient
    {H G : GroupScheme (Spec R)} [IsAffine G.X.left]
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H) (i : H ⟶ G)
    [Mono i.hom.hom] (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map i)) :
    CommGroupScheme (Spec R) :=
  (isCentral_of_isMultiplicativeType hH i I hI hc).commGroupScheme

@[simp]
theorem commGroupSchemeOfNilpotentQuotient_toGrp
    {H G : GroupScheme (Spec R)} [IsAffine G.X.left]
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H) (i : H ⟶ G)
    [Mono i.hom.hom] (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map i)) :
    (commGroupSchemeOfNilpotentQuotient hH i I hI hc).toGrp = H := rfl

end MultiplicativeTypeAffineInfinitesimalCentrality
end Langlands.GroupScheme
