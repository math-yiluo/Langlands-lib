import Langlands.GaloisCohomology.CompactSupport.Transport
import Langlands.GaloisCohomology.Global.PoitouTate.FinitePlaces
import Langlands.GaloisCohomology.CompactSupport.BaseCase

/-!
# Open subgroups of `G_S` and their fixed fields

Let `L ⊆ K_S` be a finite extension of `K`, `U ⊆ G_S` the open subgroup fixing it and
`S_L` the places of `L` above `S`. The isomorphism `U ≅ G_{S_L}(L)` (`fixingOpenSubgroupEquiv`)
matches the Mackey family of local groups of `U` (indexed by the double cosets
`U \ G_S / G_{K_v}`, `v ∈ S`) with the localizations of `G_{S_L}(L)` at the places of `S_L`
(`mackeyPlaceEquiv`, `fixingOpenSubgroupEquiv_mackeyConj_eq_localizationHom`) for the embeddings
`placeEmbeddingsOver hL ι ι₀` of `Ω` at the places of `L` (those of the Mackey correspondence above
`S`, those of `ι₀` elsewhere), and `μ_N(L_{S_L})` with `μ_N(K_S)` (`dualizingModuleResIso`). So the
cohomology with compact support of `G_{S_L}(L)` with coefficients `μ_N` is that of `U` with its
Mackey family (`mackeyCompactTransport`), compatibly with cup products with `ℤ/N`
(`compactTransport_compactCupRes` of `Langlands.GaloisCohomology.CompactSupport.Transport`).

Consequence (`bijective_compactZmodDualityMap_fixingOpenSubgroup`): if the duality for `ℤ/N` with
compact support holds for `G_{S_L}(L)` with a trace generating `Hom(H_c³(G_{S_L}(L), μ_N), ℤ/N)`, it
holds for `U` with every surjective trace, since the two traces then differ by a unit
(`isUnit_of_surjective_of_eq_mul` of `Langlands.Cohomology.Profinite.Duality.DualModule`,
`bijective_compactZmodDualityMap_of_transport`).
-/

namespace Langlands.GaloisCohomology.PoitouTate

open CategoryTheory MonoidalCategory Langlands.ProfiniteCohomology Langlands.Galois NumberField
  IsDedekindDomain GaloisGroupUnramifiedOutside

universe u

noncomputable section

section TransportDuality

variable {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {ι ι' : Type u} {H : ι → Type u}
  {H' : ι' → Type u} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)]
  [∀ j, Group (H' j)] [∀ j, TopologicalSpace (H' j)] [∀ j, IsTopologicalGroup (H' j)]
  (φ : ∀ i, H i →ₜ* G) (φ' : ∀ j, H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι')
  (ψ : ∀ i, H i ≃ₜ* H' (e i)) (hcomm : ∀ i h, θ (φ i h) = φ' (e i) (ψ i h))
  {n : ℕ} {D' : Rep.{u} (ULift.{u} ℤ) G'} [IsSmoothRep D'] {D : Rep.{u} (ULift.{u} ℤ) G}
  [IsSmoothRep D] (hD' : ∀ d : D', n • d = 0) (hD : ∀ d : D, n • d = 0)
  (f : Rep.res (θ : G →* G') D' ≅ D)

/-- The duality for `ℤ/n` with compact support transports along isomorphisms of groups, families and
dualizing modules, the traces being allowed to differ by a unit. -/
theorem bijective_compactZmodDualityMap_of_transport {r s : ℕ} (h : r + s = 3)
    (T' : compactSupportCohomologyRes φ' D' 3 →+ ZMod n)
    (T : compactSupportCohomologyRes φ D 3 →+ ZMod n) (c : ZMod n) (hc : IsUnit c)
    (hT : ∀ w, T ((compactTransport φ φ' θ e ψ hcomm f.hom 3).hom w) = c * T' w)
    (hbij : Function.Bijective (compactZmodDualityMap φ' D' hD' T' h)) :
    Function.Bijective (compactZmodDualityMap φ D hD T h) := by
  have hX : IsIso (map (θ : G →ₜ* G') (zmodRepResIso θ n).hom r) :=
    isIso_map_of_mulEquiv θ.toMulEquiv θ.continuous θ.symm.continuous (zmodRepResIso θ n).hom
      (Function.bijective_iff_has_inverse.2 ⟨(zmodRepResIso θ n).inv.hom, fun _ => rfl,
        fun _ => rfl⟩) r
  let eX : cohomology (zmodRep.{u} G' n) r ≃+ cohomology (zmodRep.{u} G n) r :=
    (asIso (map (θ : G →ₜ* G') (zmodRepResIso θ n).hom r)).toLinearEquiv.toAddEquiv
  let eY := (compactTransportIso φ φ' θ e ψ hcomm f s).toLinearEquiv.toAddEquiv
  let eW := (compactTransportIso φ φ' θ e ψ hcomm f 3).toLinearEquiv.toAddEquiv
  exact bijective_of_transport
    (bilinAddHom (compactCupRes φ' (zmodMulPairingRight n D' hD') ((Nat.add_comm s r).trans h)))
    (bilinAddHom (compactCupRes φ (zmodMulPairingRight n D hD) ((Nat.add_comm s r).trans h)))
    T' T eX eY eW (fun y x => (compactTransport_compactCupRes φ φ' θ e ψ hcomm f.hom
      (zmodRepResIso θ n).hom f.hom (zmodMulPairingRight n D' hD') (zmodMulPairingRight n D hD)
      (zmodMulPairingRight_res θ n hD' hD f.hom) ((Nat.add_comm s r).trans h) y x).symm)
    c hc hT hbij

end TransportDuality

section Embeddings

open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

variable {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) (ι : PlaceEmbeddings K Ω)

/-- The embeddings of `Ω` at the places of `L` above `S` given by the Mackey correspondence: at the
place attached to the double coset of `x` over `v`, the embedding `localEmbeddingOver hL ι v x`. -/
def mackeyEmbedding : ∀ w : finitePlacesAbove L S,
    Ω →ₐ[L] AlgebraicClosure ((w : HeightOneSpectrum (𝓞 L)).adicCompletion L) :=
  Equiv.piCongrLeft (fun w : finitePlacesAbove L S =>
      Ω →ₐ[L] AlgebraicClosure ((w : HeightOneSpectrum (𝓞 L)).adicCompletion L))
    (mackeyPlaceEquiv S hL ι) fun p => localEmbeddingOver hL ι p.1 p.2.out

theorem mackeyEmbedding_mackeyPlaceEquiv (p : Σ v : S, MackeyDoubleCoset
      (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (localizationHom ι S v).toMonoidHom) :
    mackeyEmbedding hL ι (mackeyPlaceEquiv S hL ι p) = localEmbeddingOver hL ι p.1 p.2.out :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

open Classical in
/-- Embeddings of `Ω` at the places of `L`: at the places above `S` those of the Mackey
correspondence for `ι` (`mackeyEmbedding`), elsewhere those of `ι₀`. -/
def placeEmbeddingsOver (ι₀ : PlaceEmbeddings L Ω) : PlaceEmbeddings L Ω where
  finite w := if hw : w ∈ finitePlacesAbove L S then mackeyEmbedding hL ι ⟨w, hw⟩ else ι₀.finite w
  infinite := ι₀.infinite

theorem placeEmbeddingsOver_finite (ι₀ : PlaceEmbeddings L Ω) (w : finitePlacesAbove L S) :
    (placeEmbeddingsOver hL ι ι₀).finite w = mackeyEmbedding hL ι w :=
  dite_eq_left_of_eq_true (eq_true w.2)

/-- Under `U ≅ G_{S_L}(L)`, conjugation by `x` on the Mackey subgroup at `(v, UxG_{K_v})` is the
localization of `G_{S_L}(L)` at the attached place for the embeddings `placeEmbeddingsOver hL ι ι₀`. -/
theorem fixingOpenSubgroupEquiv_mackeyConj_eq_localizationHom [IsGalois L Ω]
    (ι₀ : PlaceEmbeddings L Ω) (p : Σ v : S, MackeyDoubleCoset
      (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (localizationHom ι S v).toMonoidHom)
    (σ : mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (localizationHom ι S p.1).toMonoidHom p.2.out) :
    fixingOpenSubgroupEquiv S hL (mackeyConj (fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (localizationHom ι S p.1).toMonoidHom
          p.2.out σ) =
      localizationHom (placeEmbeddingsOver hL ι ι₀) (finitePlacesAbove L S)
        (mackeyPlaceEquiv S hL ι p) (mackeyLocalEquiv hL ι p.1 p.2.out σ) := by
  have hE : (placeEmbeddingsOver hL ι ι₀).finite (mackeyPlaceEquiv S hL ι p : HeightOneSpectrum (𝓞 L)) =
      localEmbeddingOver hL ι p.1 p.2.out :=
    (placeEmbeddingsOver_finite hL ι ι₀ (mackeyPlaceEquiv S hL ι p)).trans
      (mackeyEmbedding_mackeyPlaceEquiv hL ι p)
  refine (fixingOpenSubgroupEquiv_mackeyConj hL ι p.1 p.2.out σ).trans ?_
  exact (congrArg (fun j : Ω →ₐ[L] AlgebraicClosure
      ((mackeyPlaceEquiv S hL ι p : HeightOneSpectrum (𝓞 L)).adicCompletion L) =>
    decompositionHom ((mackeyPlaceEquiv S hL ι p : HeightOneSpectrum (𝓞 L)).adicCompletion L)
      (j.comp (maximalUnramifiedOutside L Ω (finitePlacesAbove L S)).val)
      (mackeyLocalEquiv hL ι p.1 p.2.out σ)) hE).symm

end Embeddings

section Dualizing

variable {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) (N : ℕ)

theorem maximalUnramifiedOutsideEquiv_symm_apply_apply
    (σ : (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)))
    (y : maximalUnramifiedOutside L Ω (finitePlacesAbove L S)) :
    (maximalUnramifiedOutsideEquiv hL).symm (fixingOpenSubgroupEquiv S hL σ y) =
      (σ : GaloisGroupUnramifiedOutside K Ω S) ((maximalUnramifiedOutsideEquiv hL).symm y) := by
  apply (maximalUnramifiedOutsideEquiv hL).injective
  rw [AlgEquiv.apply_symm_apply, maximalUnramifiedOutsideEquiv_apply_apply, AlgEquiv.apply_symm_apply]

/-- `μ_N(L_{S_L}) = μ_N(K_S)` as modules of `U ≅ G_{S_L}(L)`, `U` the subgroup fixing `L`. -/
def dualizingModuleResIso :
    Rep.res ((fixingOpenSubgroupEquiv S hL : (fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)) →* GaloisGroupUnramifiedOutside L Ω
          (finitePlacesAbove L S))) (dualizingModule L Ω (finitePlacesAbove L S) N) ≅
      Rep.res (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (dualizingModule K Ω S N) where
  hom := Rep.ofHom ⟨(uliftIntLinearMap (MonoidHom.toAdditive
      (restrictRootsOfUnity (maximalUnramifiedOutsideEquiv hL).symm N)) :
        Additive (rootsOfUnity N (maximalUnramifiedOutside L Ω (finitePlacesAbove L S))) →ₗ[ULift.{u} ℤ]
          Additive (rootsOfUnity N (maximalUnramifiedOutside K Ω S))), fun σ => LinearMap.ext
    fun ζ => by
      apply (Additive.toMul (α := rootsOfUnity N (maximalUnramifiedOutside K Ω S))).injective
      apply Subtype.ext
      apply Units.ext
      change (maximalUnramifiedOutsideEquiv hL).symm (fixingOpenSubgroupEquiv S hL σ
          (((Additive.toMul (α := rootsOfUnity N (maximalUnramifiedOutside L Ω
            (finitePlacesAbove L S))) ζ : (maximalUnramifiedOutside L Ω (finitePlacesAbove L S))ˣ)) :
              maximalUnramifiedOutside L Ω (finitePlacesAbove L S))) =
        (σ : GaloisGroupUnramifiedOutside K Ω S) ((maximalUnramifiedOutsideEquiv hL).symm
          (((Additive.toMul (α := rootsOfUnity N (maximalUnramifiedOutside L Ω
            (finitePlacesAbove L S))) ζ : (maximalUnramifiedOutside L Ω (finitePlacesAbove L S))ˣ)) :
              maximalUnramifiedOutside L Ω (finitePlacesAbove L S)))
      exact maximalUnramifiedOutsideEquiv_symm_apply_apply hL σ _⟩
  inv := Rep.ofHom ⟨(uliftIntLinearMap (MonoidHom.toAdditive
      (restrictRootsOfUnity (maximalUnramifiedOutsideEquiv hL) N)) :
        Additive (rootsOfUnity N (maximalUnramifiedOutside K Ω S)) →ₗ[ULift.{u} ℤ]
          Additive (rootsOfUnity N (maximalUnramifiedOutside L Ω (finitePlacesAbove L S)))),
      fun σ => LinearMap.ext
    fun ζ => by
      apply (Additive.toMul (α := rootsOfUnity N (maximalUnramifiedOutside L Ω
        (finitePlacesAbove L S)))).injective
      apply Subtype.ext
      apply Units.ext
      change (maximalUnramifiedOutsideEquiv hL) ((σ : GaloisGroupUnramifiedOutside K Ω S)
          (((Additive.toMul (α := rootsOfUnity N (maximalUnramifiedOutside K Ω S)) ζ :
            (maximalUnramifiedOutside K Ω S)ˣ)) : maximalUnramifiedOutside K Ω S)) =
        fixingOpenSubgroupEquiv S hL σ ((maximalUnramifiedOutsideEquiv hL)
          (((Additive.toMul (α := rootsOfUnity N (maximalUnramifiedOutside K Ω S)) ζ :
            (maximalUnramifiedOutside K Ω S)ˣ)) : maximalUnramifiedOutside K Ω S))
      exact maximalUnramifiedOutsideEquiv_apply_apply hL σ _⟩
  hom_inv_id := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun ζ => ?_))
    apply (Additive.toMul (α := rootsOfUnity N (maximalUnramifiedOutside L Ω
      (finitePlacesAbove L S)))).injective
    apply Subtype.ext
    apply Units.ext
    exact (maximalUnramifiedOutsideEquiv hL).apply_symm_apply _
  inv_hom_id := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun ζ => ?_))
    apply (Additive.toMul (α := rootsOfUnity N (maximalUnramifiedOutside K Ω S))).injective
    apply Subtype.ext
    apply Units.ext
    exact (maximalUnramifiedOutsideEquiv hL).symm_apply_apply _

end Dualizing

section Duality

variable {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω] [IsGalois L Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) (ι : PlaceEmbeddings K Ω)
  (ι₀ : PlaceEmbeddings L Ω) (N : ℕ)
  [hDU : IsSmoothRep (Rep.res (fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N))]

/-- The cohomology with compact support of `G_{S_L}(L)` (places above `S`, embeddings
`placeEmbeddingsOver hL ι ι₀`) with coefficients `μ_N` is that of the subgroup `U` of `G_S` fixing
`L`, with its Mackey family of local groups. -/
def mackeyCompactTransport (n : ℕ) :
    compactSupportCohomologyRes (localFamily (placeEmbeddingsOver hL ι ι₀) (finitePlacesAbove L S))
        (dualizingModule L Ω (finitePlacesAbove L S) N) n ≅
      compactSupportCohomologyRes (mackeyFamily (fixingOpenSubgroup S hL) (localFamily ι S))
        (Rep.res (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
          (dualizingModule K Ω S N)) n :=
  compactTransportIso (mackeyFamily (fixingOpenSubgroup S hL) (localFamily ι S))
    (localFamily (placeEmbeddingsOver hL ι ι₀) (finitePlacesAbove L S))
    (fixingOpenSubgroupEquiv S hL) (mackeyPlaceEquiv S hL ι)
    (fun p => mackeyLocalEquiv hL ι p.1 p.2.out)
    (fun p σ => fixingOpenSubgroupEquiv_mackeyConj_eq_localizationHom hL ι ι₀ p σ)
    (dualizingModuleResIso hL N) n

/-- **Duality for `ℤ/N` over an open subgroup of `G_S`.** If the duality for `ℤ/N` with compact
support holds for `G_{S_L}(L)` with a trace `T'` generating `Hom(H_c³(G_{S_L}(L), μ_N), ℤ/N)`, it holds
for the subgroup `U` of `G_S` fixing `L`, with its Mackey family, for every surjective trace. -/
theorem bijective_compactZmodDualityMap_fixingOpenSubgroup {r s : ℕ} (h : r + s = 3)
    (T' : compactSupportCohomologyRes (localFamily (placeEmbeddingsOver hL ι ι₀)
      (finitePlacesAbove L S)) (dualizingModule L Ω (finitePlacesAbove L S) N) 3 →+ ZMod N)
    (hgen : ∀ χ : compactSupportCohomologyRes (localFamily (placeEmbeddingsOver hL ι ι₀)
        (finitePlacesAbove L S)) (dualizingModule L Ω (finitePlacesAbove L S) N) 3 →+ ZMod N,
      ∃ c : ZMod N, ∀ y, χ y = c * T' y)
    (hbij : Function.Bijective (compactZmodDualityMap (localFamily (placeEmbeddingsOver hL ι ι₀)
      (finitePlacesAbove L S)) (dualizingModule L Ω (finitePlacesAbove L S) N)
        (nsmul_dualizingModule (finitePlacesAbove L S) N) T' h))
    (T : compactSupportCohomologyRes (mackeyFamily (fixingOpenSubgroup S hL) (localFamily ι S))
      (Rep.res (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (dualizingModule K Ω S N)) 3 →+ ZMod N)
    (hT : Function.Surjective T) :
    Function.Bijective (compactZmodDualityMap (mackeyFamily (fixingOpenSubgroup S hL)
      (localFamily ι S)) (Rep.res (fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N))
          (nsmul_dualizingModule S N) T h) := by
  have hc := hgen (T.comp (mackeyCompactTransport hL ι ι₀ N 3).hom.hom.toAddMonoidHom)
  have hsurj : Function.Surjective
      (T.comp (mackeyCompactTransport hL ι ι₀ N 3).hom.hom.toAddMonoidHom) := fun z =>
    (hT z).elim fun y hy => ⟨(mackeyCompactTransport hL ι ι₀ N 3).inv.hom y,
      (congrArg T (hom_apply_hom_apply_of_comp_eq
        (mackeyCompactTransport hL ι ι₀ N 3).inv_hom_id y)).trans hy⟩
  refine Exists.elim hc fun c hc => ?_
  exact bijective_compactZmodDualityMap_of_transport
    (mackeyFamily (fixingOpenSubgroup S hL) (localFamily ι S))
    (localFamily (placeEmbeddingsOver hL ι ι₀) (finitePlacesAbove L S))
    (fixingOpenSubgroupEquiv S hL) (mackeyPlaceEquiv S hL ι)
    (fun p => mackeyLocalEquiv hL ι p.1 p.2.out)
    (fun p σ => fixingOpenSubgroupEquiv_mackeyConj_eq_localizationHom hL ι ι₀ p σ)
    (nsmul_dualizingModule (finitePlacesAbove L S) N) (nsmul_dualizingModule S N)
    (dualizingModuleResIso hL N) h T' T c (isUnit_of_surjective_of_eq_mul _ T' hsurj c hc) hc hbij

end Duality

end

end Langlands.GaloisCohomology.PoitouTate
