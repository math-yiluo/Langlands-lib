import Langlands.Automorphic.WeakInductionAssociationStatement
import Langlands.Global.Arithmetic.GeneralPositionMackeyProof
import Langlands.Global.Arithmetic.HarrisDatumArchimedean
import Langlands.ClassField.Global.IdeleGaloisDescentProof
import Langlands.Global.Factors.RelativeWeilLocalEuler
import Langlands.Representation.Filtration.CentralEigenspaceSplitting

/-!
# Irreducibility of induced reciprocity representations from relative regularity

For a tower `E ⊆ E' ⊆ L` of number fields with `E` totally complex and `L / E` Galois, and a
Hecke character `ξ` of `E'` that is relatively regular over `E` (Harris 1998, Definition 2.3),
the representation `Ind_{W_{L/E'}}^{W_{L/E}} (ξ ∘ τ_{E'})` of the relative Weil group is
irreducible. This is the irreducibility of `S(X)` in Henniart (2000), §3.4.

The proof is Mackey's criterion for the normal subgroup `C_L`: an element of `W_{L/E}` that
stabilizes `ξ ∘ N_{L/E'}` on `C_L` must lie in `W_{L/E'}`. Ideles concentrated at one
archimedean place of `L` separate the conjugates, because the archimedean components of `ξ` at
distinct places of `E'` above one place of `E` are distinct.

The character `rangeReciprocityCharacter` is `ξ ∘ τ_{E'}` moved to the image of `W_{L/E'}` in
`W_{L/E}`, and `inducedReciprocityRepresentationEquiv` identifies its induction with
`inducedReciprocityRepresentation`.
-/

noncomputable section

universe u uV

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField NumberField.LiesOver
open Langlands.Global Langlands.Global.AdelicFunctoriality

namespace InducedReciprocityIrreducible

section Tower

variable {E E' L : Type*} [Field E] [Field E'] [Field L] [Algebra E E'] [Algebra E' L]
  [Algebra E L] [IsScalarTower E E' L]
  (τ : NumberField.InfinitePlace E) (w : NumberField.InfinitePlace E') (p : NumberField.InfinitePlace L)
  [w.LiesOver τ] [p.LiesOver w] [p.LiesOver τ]

/-- The archimedean completion maps of a tower compose. -/
theorem completionMap_comp :
    (LiesOver.completionMap (v := w) (w := p)).comp (LiesOver.completionMap (v := τ) (w := w)) =
      LiesOver.completionMap (v := τ) (w := p) := by
  refine RingHom.ext fun x => congrFun ((NumberField.InfinitePlace.Completion.denseRange_coe τ).equalizer
    ((LiesOver.continuous_completionMap (v := w) (w := p)).comp
      (LiesOver.continuous_completionMap (v := τ) (w := w)))
    (LiesOver.continuous_completionMap (v := τ) (w := p)) (funext fun y => ?_)) x
  change LiesOver.completionMap (v := w) (w := p)
      (LiesOver.completionMap (v := τ) (w := w) (algebraMap E τ.Completion (WithAbs.ofAbs y))) =
    LiesOver.completionMap (v := τ) (w := p) (algebraMap E τ.Completion (WithAbs.ofAbs y))
  rw [IdeleGaloisDescentProof.completionMap_algebraMap,
    IdeleGaloisDescentProof.completionMap_algebraMap,
    IdeleGaloisDescentProof.completionMap_algebraMap, IsScalarTower.algebraMap_apply E E' L y.ofAbs]

end Tower

section Norm

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- The norm of an idele concentrated at one archimedean place `q` is concentrated at the
place below `q`, with the local norm as its component. -/
theorem ideleNorm_ofCompletion (p : NumberField.InfinitePlace K) (q : NumberField.InfinitePlace L) [q.LiesOver p]
    (y : q.Completionˣ) :
    ideleNorm (K := K) (IdeleGroup.ofCompletion (𝓞 L) L q y) =
      IdeleGroup.ofCompletion (𝓞 K) K p (InfiniteExtension.localUnitNorm p q y) := by
  classical
  apply Units.ext
  apply Prod.ext
  · funext p'
    change (∏ r : InfinitePlacesAbove L p', InfiniteExtension.localNorm p' r.1
        (Pi.mulSingle q (y : q.Completion) r.1)) =
      Pi.mulSingle p (InfiniteExtension.localNorm p q (y : q.Completion)) p'
    by_cases hp : p' = p
    · subst hp
      rw [Pi.mulSingle_eq_same, Finset.prod_eq_single (⟨q, inferInstance⟩ : InfinitePlacesAbove L p')]
      · rw [Pi.mulSingle_eq_same]
      · intro r _ hr
        have hrq : r.1 ≠ q := fun h => hr (Subtype.ext h)
        rw [Pi.mulSingle_eq_of_ne hrq, map_one]
      · simp
    · rw [Pi.mulSingle_eq_of_ne hp]
      refine Finset.prod_eq_one fun r _ => ?_
      have hrq : r.1 ≠ q := by
        intro h
        apply hp
        have h1 := NumberField.InfinitePlace.LiesOver.comap_eq r.1 p'
        have h2 := NumberField.InfinitePlace.LiesOver.comap_eq q p
        rw [h] at h1
        exact h1.symm.trans h2
      rw [Pi.mulSingle_eq_of_ne hrq, map_one]
  · exact map_one (finiteAdeleNorm (K := K) (L := L))

/-- The same on idele classes. -/
theorem ideleClassNorm_ofCompletion (p : NumberField.InfinitePlace K) (q : NumberField.InfinitePlace L) [q.LiesOver p]
    (y : q.Completionˣ) :
    ideleClassNorm (K := K) (IdeleClassGroup.ofCompletion (𝓞 L) L q y) =
      IdeleClassGroup.ofCompletion (𝓞 K) K p (InfiniteExtension.localUnitNorm p q y) := by
  change ideleClassNorm (K := K) (QuotientGroup.mk (IdeleGroup.ofCompletion (𝓞 L) L q y)) = _
  rw [ideleClassNorm_mk, ideleNorm_ofCompletion p q y]
  rfl

end Norm

section Separation

variable {E E' L : Type*} [Field E] [NumberField E] [IsTotallyComplex E] [Field E']
  [NumberField E'] [Field L] [NumberField L] [Algebra E E'] [Algebra E L] [Algebra E' L]
  [IsScalarTower E E' L]

omit [NumberField E] [NumberField E'] [NumberField L] in
/-- If the places `p ∘ σ` and `p` of `L` restrict to the same place of `E'`, then `σ` fixes
`E'`: otherwise the two embeddings of `E'` would be complex conjugate, and their common
restriction to `E` would be real. -/
theorem fixes_of_comap_eq (σ : L ≃ₐ[E] L) (p : NumberField.InfinitePlace L)
    (hp : (p.comap σ.toRingEquiv.toRingHom).comap (algebraMap E' L) =
      p.comap (algebraMap E' L)) (x : E') :
    σ (algebraMap E' L x) = algebraMap E' L x := by
  have hc := IsTotallyComplex.isComplex (p.comap (algebraMap E L))
  rw [← NumberField.InfinitePlace.mk_embedding p] at hp hc
  rw [NumberField.InfinitePlace.comap_mk, NumberField.InfinitePlace.comap_mk,
    NumberField.InfinitePlace.comap_mk, NumberField.InfinitePlace.mk_eq_iff] at hp
  rw [NumberField.InfinitePlace.comap_mk] at hc
  rcases hp with hp | hp
  · exact p.embedding.injective (RingHom.congr_fun hp x)
  · exfalso
    refine NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hc
      (NumberField.InfinitePlace.isReal_mk_iff.mpr
        (ComplexEmbedding.isReal_iff.mpr (RingHom.ext fun e => ?_)))
    rw [ComplexEmbedding.conjugate_coe_eq]
    have he := RingHom.congr_fun hp (algebraMap E E' e)
    simp only [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply] at he
    change (starRingEnd ℂ) (p.embedding (σ (algebraMap E L e))) = _ at he
    simpa only [RingHom.comp_apply, σ.commutes] using he

omit [NumberField E] in
/-- An idele class concentrated at one archimedean place `r` of `L`, with component the image
of `y ∈ E_τˣ`, has norm to `E'` concentrated at the place `w` below `r`, with component the
image of `y`: the local degree is one because `w` is complex. -/
theorem ideleClassNorm_ofCompletion_completionMap (τ : NumberField.InfinitePlace E)
    (w : NumberField.InfinitePlace E') (r : NumberField.InfinitePlace L) [w.LiesOver τ]
    [r.LiesOver w] [r.LiesOver τ] (y : τ.Completionˣ) :
    ideleClassNorm (K := E') (IdeleClassGroup.ofCompletion (𝓞 L) L r
        (Units.map (LiesOver.completionMap (v := τ) (w := r)).toMonoidHom y)) =
      IdeleClassGroup.ofCompletion (𝓞 E') E' w
        (Units.map (LiesOver.completionMap (v := τ) (w := w)).toMonoidHom y) := by
  rw [ideleClassNorm_ofCompletion w r]
  congr 1
  apply Units.ext
  have : IsTotallyComplex E' := isTotallyComplex_of_algebra E E'
  have hunr : r.IsUnramified E' := NumberField.InfinitePlace.isUnramified_iff.mpr
    (Or.inr (by rw [NumberField.InfinitePlace.LiesOver.comap_eq r w];
                exact IsTotallyComplex.isComplex w))
  change InfiniteExtension.localNorm w r (LiesOver.completionMap (v := τ) (w := r) (y : τ.Completion)) =
    LiesOver.completionMap (v := τ) (w := w) (y : τ.Completion)
  rw [← completionMap_comp τ w r, RingHom.comp_apply, InfiniteExtension.localNorm_algebraMap,
    hunr.finrank_eq_one w, pow_one]

/-- Harris's relative regularity separates the Galois conjugates of `ξ ∘ N_{L/E'}`: an
automorphism of `L / E` that preserves `ξ ∘ N_{L/E'}` on `C_L` fixes `E'`. -/
theorem fixes_of_ideleClassNorm_invariant (ξ : HeckeCharacter E')
    (hξ : Harris.IsRelativelyRegular E ξ) (σ : L ≃ₐ[E] L)
    (hσ : ∀ a : IdeleClassGroup (𝓞 L) L,
      ξ (ideleClassNorm (K := E') (ideleClassEquiv σ.toRingEquiv a)) =
        ξ (ideleClassNorm (K := E') a))
    (x : E') : σ (algebraMap E' L x) = algebraMap E' L x := by
  classical
  obtain ⟨p⟩ : Nonempty (NumberField.InfinitePlace L) := inferInstance
  by_contra hx
  set τ := p.comap (algebraMap E L) with hτ
  have hne : (infinitePlaceEquiv σ.toRingEquiv p).comap (algebraMap E' L) ≠
      p.comap (algebraMap E' L) :=
    fun h => hx (fixes_of_comap_eq σ p h x)
  have : p.LiesOver τ := IdeleGaloisDescentProof.liesOver_of_comap_eq rfl
  have : (infinitePlaceEquiv σ.toRingEquiv p).LiesOver τ :=
    IdeleGaloisDescentProof.liesOver_infinitePlaceEquiv σ τ p
  have : (p.comap (algebraMap E' L)).LiesOver τ :=
    IdeleGaloisDescentProof.liesOver_of_comap_eq (by
      change p.comap ((algebraMap E' L).comp (algebraMap E E')) = τ
      rw [← IsScalarTower.algebraMap_eq])
  have : ((infinitePlaceEquiv σ.toRingEquiv p).comap (algebraMap E' L)).LiesOver τ :=
    IdeleGaloisDescentProof.liesOver_of_comap_eq (by
      change (infinitePlaceEquiv σ.toRingEquiv p).comap
        ((algebraMap E' L).comp (algebraMap E E')) = τ
      rw [← IsScalarTower.algebraMap_eq]
      exact NumberField.InfinitePlace.LiesOver.comap_eq _ τ)
  have : p.LiesOver (p.comap (algebraMap E' L)) :=
    IdeleGaloisDescentProof.liesOver_of_comap_eq rfl
  have : (infinitePlaceEquiv σ.toRingEquiv p).LiesOver
      ((infinitePlaceEquiv σ.toRingEquiv p).comap (algebraMap E' L)) :=
    IdeleGaloisDescentProof.liesOver_of_comap_eq rfl
  obtain ⟨y, hy⟩ := hξ τ _ _ hne
  apply hy
  have key := hσ (IdeleClassGroup.ofCompletion (𝓞 L) L (infinitePlaceEquiv σ.toRingEquiv p)
    (Units.map (LiesOver.completionMap (v := τ)
      (w := infinitePlaceEquiv σ.toRingEquiv p)).toMonoidHom y))
  rw [ideleClassEquiv_ofCompletion σ.toRingEquiv p] at key
  have htr : Units.mapEquiv (infiniteCompletionEquiv σ.toRingEquiv p).toMulEquiv
      (Units.map (LiesOver.completionMap (v := τ)
        (w := infinitePlaceEquiv σ.toRingEquiv p)).toMonoidHom y) =
      Units.map (LiesOver.completionMap (v := τ) (w := p)).toMonoidHom y := by
    apply Units.ext
    exact IdeleGaloisDescentProof.infiniteTransport_completionMap σ τ p y
  rw [htr, ideleClassNorm_ofCompletion_completionMap τ (p.comap (algebraMap E' L)) p,
    ideleClassNorm_ofCompletion_completionMap τ
      ((infinitePlaceEquiv σ.toRingEquiv p).comap (algebraMap E' L))
      (infinitePlaceEquiv σ.toRingEquiv p)] at key
  exact key.symm

end Separation

end InducedReciprocityIrreducible

namespace RelativeWeilGroup

open InducedReciprocityIrreducible

attribute [local instance] relativeGaloisTopology

section Character

variable (c : FundamentalClass.ClassFamily.{u})
  (E E' L : Type u) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field L]
  [NumberField L] [Algebra E E'] [Algebra E L] [Algebra E' L] [IsScalarTower E E' L]
  [IsGalois E L] (h : FundamentalClass.Restriction c)

/-- The reciprocity character `ξ ∘ τ_{E'}` of `W_{L/E'}`, transported to the image of
`W_{L/E'}` in `W_{L/E}`. Inducing it to `W_{L/E}` gives the representation
`inducedReciprocityRepresentation`. -/
def rangeReciprocityCharacter (ξ : HeckeCharacter E') :
    haveI : IsGalois E' L := IsGalois.tower_top_of_isGalois E E' L
    (restrictionInclusion c E L E' h).toMonoidHom.range →* ℂˣ :=
  haveI : IsGalois E' L := IsGalois.tower_top_of_isGalois E E' L
  (reciprocityCharacter c E' L ξ).comp
    (InductionAlong.rangeInverse _ (restrictionInclusion_injective c E L E' h))

/-- On the idele classes of `L`, the inverse of the inclusion `W_{L/E'} → W_{L/E}` on its
range is the idele-class inclusion into `W_{L/E'}`. -/
theorem rangeInverse_inclusion (b : IdeleClassGroup (𝓞 L) L) :
    haveI : IsGalois E' L := IsGalois.tower_top_of_isGalois E E' L
    InductionAlong.rangeInverse (restrictionInclusion c E L E' h).toMonoidHom
        (restrictionInclusion_injective c E L E' h)
        ⟨inclusion c E L b, inclusion c E' L b, restrictionInclusion_inclusion c E L E' h b⟩ =
      inclusion c E' L b := by
  have : IsGalois E' L := IsGalois.tower_top_of_isGalois E E' L
  apply restrictionInclusion_injective c E L E' h
  exact (InductionAlong.apply_rangeInverse _ _ _).trans
    (restrictionInclusion_inclusion c E L E' h b).symm

/-- On the idele classes of `L`, the transported character is `b ↦ ξ(N_{L/E'} b)⁻¹`. -/
theorem rangeReciprocityCharacter_inclusion (ξ : HeckeCharacter E')
    (b : IdeleClassGroup (𝓞 L) L) :
    haveI : IsGalois E' L := IsGalois.tower_top_of_isGalois E E' L
    rangeReciprocityCharacter c E E' L h ξ
        ⟨inclusion c E L b, inclusion c E' L b, restrictionInclusion_inclusion c E L E' h b⟩ =
      (ξ (ideleClassNorm (K := E') b))⁻¹ := by
  have : IsGalois E' L := IsGalois.tower_top_of_isGalois E E' L
  change reciprocityCharacter c E' L ξ (InductionAlong.rangeInverse _
    (restrictionInclusion_injective c E L E' h)
      ⟨inclusion c E L b, inclusion c E' L b, restrictionInclusion_inclusion c E L E' h b⟩) = _
  rw [rangeInverse_inclusion c E E' L h b, reciprocityCharacter_apply, transfer_inclusion]

/-- The induced reciprocity representation, in any carrier universe, is equivalent to the
induction of the transported character on a line in carrier universe `0`. -/
def inducedReciprocityRepresentationEquiv (ξ : HeckeCharacter E') :
    haveI : IsGalois E' L := IsGalois.tower_top_of_isGalois E E' L
    FiniteRepresentation.Equiv (inducedReciprocityRepresentation.{u, uV} c E E' L h ξ)
      (FiniteRepresentation.induce (restrictionInclusion c E L E' h).toMonoidHom.range
        (FiniteRepresentation.characterLine.{u, 0} (rangeReciprocityCharacter c E E' L h ξ))) :=
  haveI : IsGalois E' L := IsGalois.tower_top_of_isGalois E E' L
  FiniteRepresentation.induceEquivOfEquiv _
    { toLinearEquiv := ULift.moduleEquiv.trans ULift.moduleEquiv.symm
      isIntertwining' := fun _ => by ext; rfl }

end Character

section Irreducible

variable (c : FundamentalClass.ClassFamily.{u})
  (E E' L : Type u) [Field E] [NumberField E] [IsTotallyComplex E] [Field E']
  [NumberField E'] [Field L] [NumberField L] [Algebra E E'] [Algebra E L] [Algebra E' L]
  [IsScalarTower E E' L] [IsGalois E L]
  (h : FundamentalClass.Restriction c)

/-- An element of `W_{L/E}` stabilizes the transported character on `C_L` exactly when it
lies in the image of `W_{L/E'}`, if `E` is totally complex and `ξ` is relatively regular. -/
theorem rangeReciprocityCharacter_exactStabilizer (ξ : HeckeCharacter E')
    (hξ : Harris.IsRelativelyRegular E ξ) :
    haveI : IsGalois E' L := IsGalois.tower_top_of_isGalois E E' L
    ∃ hNH : (inclusion c E L).range ≤ (restrictionInclusion c E L E' h).toMonoidHom.range,
      ∀ a : RelativeWeilGroup c E L,
        haveI : (inclusion c E L).range.Normal := ideleClassSubgroup_normal c E L
        ((rangeReciprocityCharacter c E E' L h ξ).comp (Subgroup.inclusion hNH)).comp
            (MulAut.conjNormal a⁻¹).toMonoidHom =
          (rangeReciprocityCharacter c E E' L h ξ).comp (Subgroup.inclusion hNH) ↔
        a ∈ (restrictionInclusion c E L E' h).toMonoidHom.range := by
  have : IsGalois E' L := IsGalois.tower_top_of_isGalois E E' L
  have : (inclusion c E L).range.Normal := ideleClassSubgroup_normal c E L
  have hNH : (inclusion c E L).range ≤ (restrictionInclusion c E L E' h).toMonoidHom.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨inclusion c E' L b, restrictionInclusion_inclusion c E L E' h b⟩
  have hψ : ∀ b : IdeleClassGroup (𝓞 L) L,
      (rangeReciprocityCharacter c E E' L h ξ).comp (Subgroup.inclusion hNH)
          ⟨inclusion c E L b, b, rfl⟩ = (ξ (ideleClassNorm (K := E') b))⁻¹ :=
    fun b => rangeReciprocityCharacter_inclusion c E E' L h ξ b
  refine ⟨hNH, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · have hσ : ∀ b : IdeleClassGroup (𝓞 L) L,
        ξ (ideleClassNorm (K := E')
            (ideleClassEquiv (projection c E L a⁻¹).toRingEquiv b)) =
          ξ (ideleClassNorm (K := E') b) := by
      intro b
      have hb := DFunLike.congr_fun ha ⟨inclusion c E L b, b, rfl⟩
      have hconj : MulAut.conjNormal a⁻¹ (⟨inclusion c E L b, b, rfl⟩ : (inclusion c E L).range) =
          ⟨inclusion c E L (ideleClassEquiv (projection c E L a⁻¹).toRingEquiv b), _, rfl⟩ := by
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        exact conjugation c E L a⁻¹ b
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hb
      rw [hconj] at hb
      have h1 := hψ (ideleClassEquiv (projection c E L a⁻¹).toRingEquiv b)
      have h2 := hψ b
      simp only [MonoidHom.comp_apply] at h1 h2
      rw [h1, h2] at hb
      exact inv_injective hb
    have hfix := fixes_of_ideleClassNorm_invariant ξ hξ (projection c E L a⁻¹) hσ
    let σ' : L ≃ₐ[E'] L := AlgEquiv.ofRingEquiv (f := (projection c E L a⁻¹).toRingEquiv) hfix
    have hmem : a⁻¹ ∈ (restrictionInclusion c E L E' h).toMonoidHom.range := by
      rw [range_restrictionInclusion]
      exact ⟨σ', AlgEquiv.ext fun x => rfl⟩
    simpa using Subgroup.inv_mem _ hmem
  · refine MonoidHom.ext fun n => ?_
    have hn : Subgroup.inclusion hNH (MulAut.conjNormal a⁻¹ n) =
        (⟨a, ha⟩ : (restrictionInclusion c E L E' h).toMonoidHom.range)⁻¹ *
          Subgroup.inclusion hNH n * ⟨a, ha⟩ :=
      Subtype.ext (by
        simp only [Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv,
          MulAut.conjNormal_apply, inv_inv])
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hn, map_mul, map_mul, map_inv, inv_mul_cancel_comm]

/-- Henniart (2000), §3.4: for `E` totally complex and `ξ` relatively regular over `E`
(Harris 1998, Definition 2.3), the representation `Ind_{W_{L/E'}}^{W_{L/E}} (ξ ∘ τ_{E'})`
is irreducible. -/
theorem inducedReciprocityRepresentation_isIrreducible (ξ : HeckeCharacter E')
    (hξ : Harris.IsRelativelyRegular E ξ) :
    (inducedReciprocityRepresentation.{u, uV} c E E' L h ξ).IsIrreducible := by
  have : IsGalois E' L := IsGalois.tower_top_of_isGalois E E' L
  have : (inclusion c E L).range.Normal := ideleClassSubgroup_normal c E L
  obtain ⟨hNH, hexact⟩ := rangeReciprocityCharacter_exactStabilizer c E E' L h ξ hξ
  exact (CentralEigenspaceSplitting.isIrreducible_iff_of_equiv
    (inducedReciprocityRepresentationEquiv c E E' L h ξ)).mpr
    (GeneralPosition.induce_irreducible_of_exactStabilizer _ _ hNH _ hexact)

end Irreducible

end RelativeWeilGroup

end Langlands.ClassField.Global
