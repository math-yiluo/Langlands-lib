import Langlands.Correspondence.Laumon.SpecialCovers
import Langlands.Correspondence.Laumon.UnramifiedLines

/-!
# The Katz–Gabber canonical extension: the bridge (b4)

Laumon (1987), Théorème (2.2.2.2), p. 157 (after Katz 1986, (1.4.8)–(1.4.11) and
(1.5.3)–(1.5.7), pp. 81–86): the map from the Galois group of the punctured henselian trait at
`0` to the quotient of `π₁(𝔾_m)` classifying the covers tamely ramified at `∞` is injective and
has a unique continuous retraction extending the geometric one; the canonical extension of a
`π₁(η)`-module `V` is the lisse sheaf on `𝔾_m`, tame at `∞`, whose stalk is `V` with
`π₁(𝔾_m)` acting through the retraction. This module defines the retraction property, the
monodromy representation of `π₁(𝔾_m)` on the stalk of a lisse sheaf, the canonical extension
of a continuous `ℓ`-adic representation along a given continuous homomorphism
`π₁(𝔾_m) → π₁(η)`, its stalk identification and its action on intertwiners, and the base change
of `𝔾_m` along an extension of the ground field. It states the retraction theorem and the
properties of the canonical extension: local monodromy, tameness, speciality, uniqueness,
functoriality, exactness, tensor products, constant twists, base change and finite geometric
monodromy.
-/

noncomputable section

universe u uH uV

open CategoryTheory AlgebraicGeometry

namespace Langlands.Henniart.Laumon

open Langlands.Henniart.LocalNumerical

section Retraction

variable (k : Type u) [Field k]

/-- A **Katz–Gabber retraction** at the end `e`: a continuous homomorphism
`r : π₁(𝔾_m, gmEndPoint k e) → Gal(Ω/K)` (`K = endField k`, `Ω = endGenericClosure k`) that is
trivial on the kernel of the quotient classifying the covers tame at the opposite end, is a
retraction of the local monodromy map `gmLocalMonodromy k e`, and maps the geometric fundamental
group into the inertia group, the automorphisms fixing `endUnramifiedField k`. -/
def IsKatzGabberRetraction (e : FourierEnd)
    (r : Aut (Scheme.FiniteEtale.fiber (gmEndPoint k e)) →* Gal(endGenericClosure k/endField k)) :
    Prop :=
  Continuous r ∧
    coverKernel (gmEndPoint k e) (IsTameCoverAt k e.opposite) ≤ r.ker ∧
    (∀ σ, r (gmLocalMonodromy k e σ) = σ) ∧
    ∀ g ∈ gmGeometricSubgroup k (gmEndPoint k e), r g ∈ (endUnramifiedField k).fixingSubgroup

end Retraction

/-- **The retraction theorem** (Laumon, Théorème (2.2.2.2), p. 157; Katz 1986, Corollaries
(1.4.9)–(1.4.11), pp. 82–83). For a finite field `k` and an end `e`, with
`N = coverKernel (gmEndPoint k e) (IsTameCoverAt k e.opposite)` the kernel of the quotient of
`π₁(𝔾_m)` classifying the covers tame at the opposite end:

1. the local monodromy map composed with the projection to this quotient is injective;
2. there is a unique Katz–Gabber retraction `r`;
3. its kernel is the kernel of the quotient classifying the special covers relative to `e`
   (so restriction identifies the special quotient of `π₁(𝔾_m)` with the Galois group of the
   end field);
4. its restriction to the geometric fundamental group is the unique continuous homomorphism from
   the geometric fundamental group to the inertia group that is trivial on `N` and retracts the
   local monodromy map on inertia. -/
def KatzGabberRetractionStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (e : FourierEnd),
    (∀ σ, gmLocalMonodromy k e σ ∈ coverKernel (gmEndPoint k e) (IsTameCoverAt k e.opposite) →
      σ = 1) ∧
    (∃! r, IsKatzGabberRetraction k e r) ∧
    ∀ r, IsKatzGabberRetraction k e r →
      r.ker = coverKernel (gmEndPoint k e) (specialCover k e) ∧
      ∀ r' : gmGeometricSubgroup k (gmEndPoint k e) →* (endUnramifiedField k).fixingSubgroup,
        Continuous r' →
        (∀ g (hg : g ∈ gmGeometricSubgroup k (gmEndPoint k e)),
          g ∈ coverKernel (gmEndPoint k e) (IsTameCoverAt k e.opposite) → r' ⟨g, hg⟩ = 1) →
        (∀ σ (hσ : σ ∈ (endUnramifiedField k).fixingSubgroup)
            (h : gmLocalMonodromy k e σ ∈ gmGeometricSubgroup k (gmEndPoint k e)),
          r' ⟨gmLocalMonodromy k e σ, h⟩ = ⟨σ, hσ⟩) →
        ∀ g (hg : g ∈ gmGeometricSubgroup k (gmEndPoint k e)),
          (r' ⟨g, hg⟩ : Gal(endGenericClosure k/endField k)) = r g

section Monodromy

variable (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime]

local notation "E" => PadicAlgCl ℓ

/-- The monodromy representation of `π₁(𝔾_m, gmEndPoint k e) = Aut (fiber (gmEndPoint k e))` on
the stalk at `gmEndPoint k e` of a lisse sheaf on `𝔾_m`, for weil-conjectures's
`universalLisseMonodromy`. -/
abbrev gmMonodromy (e : FourierEnd) (F : ProEtale.LisseSheaf ℓ (gmOpen k)) :
    Representation E (Aut (Scheme.FiniteEtale.fiber (gmEndPoint k e)))
      (ProEtale.LisseMonodromy.StalkSpace (gmEndPoint k e) F) :=
  (ProEtale.universalLisseMonodromy ℓ (gmOpen k) (endGenericClosure k)).rep (gmEndPoint k e) F

/-- The `E`-linear map of stalks at `gmEndPoint k e` of a morphism of lisse sheaves on `𝔾_m`. -/
def gmStalkMap (e : FourierEnd) {F F' : ProEtale.LisseSheaf ℓ (gmOpen k)} (φ : F ⟶ F') :
    ProEtale.LisseMonodromy.StalkSpace (gmEndPoint k e) F →ₗ[E]
      ProEtale.LisseMonodromy.StalkSpace (gmEndPoint k e) F' :=
  ((WeilCoefficients.toModuleCat ℓ).map ((ProEtale.lisseStalk ℓ (gmEndPoint k e)).map φ)).hom

variable {k ℓ}

/-- For a continuous homomorphism `r` and a representation `V` continuous for the module topology
on endomorphisms, the matrix coefficients `g ↦ φ (V (r g) v)` are continuous. -/
theorem continuous_dual_apply_comp {G : Type*} {H : Type uH} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] (V : FiniteRepresentation.{0, uH, uV} E H)
    (hV : IsLadicContinuous ℓ V) (r : G →* H) (hr : Continuous r) (φ : Module.Dual E V) (v : V) :
    Continuous fun g => φ (V.representation (r g) v) := by
  let : TopologicalSpace (Module.End E V) := moduleTopology E (Module.End E V)
  have : IsModuleTopology E (Module.End E V) := ⟨rfl⟩
  have hlin : Continuous fun A : Module.End E V => φ (A v) :=
    IsModuleTopology.continuous_of_linearMap (φ ∘ₗ LinearMap.applyₗ v)
  exact hlin.comp (hV.comp hr)

end Monodromy

section Extension

variable (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] (e : FourierEnd)
  (r : Aut (Scheme.FiniteEtale.fiber (gmEndPoint k e)) →* Gal(endGenericClosure k/endField k))
  (hr : Continuous r)

include hr

local notation "E" => PadicAlgCl ℓ

/-- For a continuous homomorphism `r : π₁(𝔾_m, gmEndPoint k e) → Gal(Ω/K)` and a continuous
`ℓ`-adic representation `V` of `Gal(Ω/K)`, there is a lisse sheaf on `𝔾_m` whose monodromy
representation is `V ∘ r`: the monodromy of weil-conjectures's `universalLisseMonodromy` is an
equivalence at `gmEndPoint k e` (`universalLisseMonodromy_isEquivalenceAt`). -/
theorem exists_lisse_monodromy_comp
    (V : FiniteRepresentation.{0, u, u + 1} E Gal(endGenericClosure k/endField k))
    (hV : IsLadicContinuous ℓ V) :
    ∃ (F : ProEtale.LisseSheaf ℓ (gmOpen k))
      (θ : ProEtale.LisseMonodromy.StalkSpace (gmEndPoint k e) F ≃ₗ[E] V),
      ∀ g v, θ (gmMonodromy k ℓ e F g v) = V.representation (r g) (θ v) :=
  (ProEtale.universalLisseMonodromy_isEquivalenceAt ℓ (gmOpen k) (endGenericClosure k)
    (gmEndPoint k e)).essSurj V (V.representation.comp r)
    (continuous_dual_apply_comp V hV r hr)

/-- **The canonical extension** along `r` (Laumon (2.2.2.2), p. 157; Katz 1986, Corollary
(1.5.7), p. 85): a lisse sheaf on `𝔾_m` whose stalk at `gmEndPoint k e` is `V`, with
`π₁(𝔾_m)` acting through `r` (chosen by `exists_lisse_monodromy_comp`). For the Katz–Gabber
retraction this is the canonical extension of `V` from the end `e`, tame at `e.opposite`. -/
def canonicalExtension (V : FiniteRepresentation.{0, u, u + 1} E Gal(endGenericClosure k/endField k))
    (hV : IsLadicContinuous ℓ V) : ProEtale.LisseSheaf ℓ (gmOpen k) :=
  (exists_lisse_monodromy_comp k ℓ e r hr V hV).choose

/-- The identification of the stalk of the canonical extension at `gmEndPoint k e` with `V`. -/
def canonicalExtensionStalkEquiv
    (V : FiniteRepresentation.{0, u, u + 1} E Gal(endGenericClosure k/endField k))
    (hV : IsLadicContinuous ℓ V) :
    ProEtale.LisseMonodromy.StalkSpace (gmEndPoint k e) (canonicalExtension k ℓ e r hr V hV) ≃ₗ[E]
      V :=
  (exists_lisse_monodromy_comp k ℓ e r hr V hV).choose_spec.choose

/-- The stalk identification carries the monodromy of `π₁(𝔾_m)` to `V ∘ r`. -/
theorem canonicalExtensionStalkEquiv_monodromy
    (V : FiniteRepresentation.{0, u, u + 1} E Gal(endGenericClosure k/endField k))
    (hV : IsLadicContinuous ℓ V) (g : Aut (Scheme.FiniteEtale.fiber (gmEndPoint k e))) (v) :
    canonicalExtensionStalkEquiv k ℓ e r hr V hV
        (gmMonodromy k ℓ e (canonicalExtension k ℓ e r hr V hV) g v) =
      V.representation (r g) (canonicalExtensionStalkEquiv k ℓ e r hr V hV v) :=
  (exists_lisse_monodromy_comp k ℓ e r hr V hV).choose_spec.choose_spec g v

/-- The inverse stalk identification carries `V ∘ r` to the monodromy of `π₁(𝔾_m)`. -/
theorem canonicalExtensionStalkEquiv_symm_monodromy
    (V : FiniteRepresentation.{0, u, u + 1} E Gal(endGenericClosure k/endField k))
    (hV : IsLadicContinuous ℓ V) (g : Aut (Scheme.FiniteEtale.fiber (gmEndPoint k e))) (w : V) :
    (canonicalExtensionStalkEquiv k ℓ e r hr V hV).symm (V.representation (r g) w) =
      gmMonodromy k ℓ e (canonicalExtension k ℓ e r hr V hV) g
        ((canonicalExtensionStalkEquiv k ℓ e r hr V hV).symm w) := by
  refine (LinearEquiv.symm_apply_eq _).mpr ?_
  exact ((congrArg (V.representation (r g))
    ((canonicalExtensionStalkEquiv k ℓ e r hr V hV).apply_symm_apply w)).symm).trans
    (canonicalExtensionStalkEquiv_monodromy k ℓ e r hr V hV g _).symm

/-- The morphism of canonical extensions of an intertwiner `f : V → W`: the morphism of lisse
sheaves whose stalk map at `gmEndPoint k e` is `f` under the stalk identifications (chosen by the
fullness of the monodromy at `gmEndPoint k e`). -/
def canonicalExtensionMap
    {V W : FiniteRepresentation.{0, u, u + 1} E Gal(endGenericClosure k/endField k)}
    (hV : IsLadicContinuous ℓ V) (hW : IsLadicContinuous ℓ W)
    (f : V.representation.IntertwiningMap W.representation) :
    canonicalExtension k ℓ e r hr V hV ⟶ canonicalExtension k ℓ e r hr W hW :=
  ((ProEtale.universalLisseMonodromy_isEquivalenceAt ℓ (gmOpen k) (endGenericClosure k)
    (gmEndPoint k e)).full
    ((canonicalExtensionStalkEquiv k ℓ e r hr W hW).symm.toLinearMap ∘ₗ f.toLinearMap ∘ₗ
      (canonicalExtensionStalkEquiv k ℓ e r hr V hV).toLinearMap)
    (fun g v =>
      (congrArg (fun x => (canonicalExtensionStalkEquiv k ℓ e r hr W hW).symm (f x))
        (canonicalExtensionStalkEquiv_monodromy k ℓ e r hr V hV g v)).trans
      ((congrArg (canonicalExtensionStalkEquiv k ℓ e r hr W hW).symm
        (LinearMap.congr_fun (f.isIntertwining' (r g))
          (canonicalExtensionStalkEquiv k ℓ e r hr V hV v))).trans
      (canonicalExtensionStalkEquiv_symm_monodromy k ℓ e r hr W hW g
        (f (canonicalExtensionStalkEquiv k ℓ e r hr V hV v)))))).choose

end Extension

section BaseChange

variable (k k₁ : Type u) [Field k] [Field k₁] [Algebra k k₁]

/-- The base change map `𝔸¹_{k₁} → 𝔸¹_k` of affine lines along `k → k₁`. -/
def lineBaseChange : affineLine k₁ ⟶ affineLine k :=
  AffineSpace.map PUnit.{u + 1} (Spec.map (CommRingCat.ofHom (algebraMap k k₁)))

/-- The base change of affine lines maps `𝔾_{m, k₁}` into `𝔾_{m, k}`: it pulls the coordinate
back to the coordinate. -/
theorem range_gmBaseChange_subset :
    Set.range ((gmOpen k₁).ι ≫ lineBaseChange k k₁) ⊆ Set.range (gmOpen k).ι := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, SetLike.mem_coe]
  have h : lineBaseChange k k₁ ⁻¹ᵁ gmOpen k = gmOpen k₁ := by
    rw [gmOpen, gmOpen, Scheme.preimage_basicOpen_top, lineBaseChange,
      AffineSpace.map_appTop_coord]
  have hy : (gmOpen k₁).ι y ∈ (gmOpen k₁ : Set (affineLine k₁)) := by
    rw [← Scheme.Opens.range_ι]
    exact ⟨y, rfl⟩
  exact (SetLike.ext_iff.mp h ((gmOpen k₁).ι y)).mpr hy

/-- The base change map `𝔾_{m, k₁} → 𝔾_{m, k}` along `k → k₁`. -/
def gmBaseChange : (gmOpen k₁ : Scheme.{u}) ⟶ gmOpen k :=
  IsOpenImmersion.lift (gmOpen k).ι ((gmOpen k₁).ι ≫ lineBaseChange k k₁)
    (range_gmBaseChange_subset k k₁)

/-- Compatible base-change data for the end field and its Galois group. The map `j` acts
coefficientwise on Laurent series, `ι` extends `j` to the separable generic closures, and the
continuous homomorphism `res` restricts automorphisms along `ι`. -/
def IsEndGaloisBaseChange (j : endField k →+* endField k₁)
    (ι : endGenericClosure k →+* endGenericClosure k₁)
    (res : Gal(endGenericClosure k₁/endField k₁) →* Gal(endGenericClosure k/endField k)) : Prop :=
  (∀ a : endField k,
    ((j a : endField k₁) : LaurentSeries k₁) = (a : LaurentSeries k).map (algebraMap k k₁)) ∧
  (∀ a : endField k, ι (algebraMap (endField k) (endGenericClosure k) a) =
    algebraMap (endField k₁) (endGenericClosure k₁) (j a)) ∧
  (∀ τ a, ι (res τ a) = τ (ι a)) ∧ Continuous res

end BaseChange

/-- **The canonical extension** (Laumon, Théorème (2.2.2.2) and the paragraph after it, p. 157;
Katz 1986, Theorem (1.5.6) and Corollary (1.5.7), pp. 85–86). Let `k` be a finite field, `ℓ` a
prime distinct from the characteristic of `k`, `e` an end and `r` a Katz–Gabber retraction at `e`.
The following hold for continuous finite-dimensional `ℓ`-adic representations `V` of the Galois
group of the end field (with carriers in the universe of the stalks).

1. the local monodromy of the canonical extension at `e` (the field monodromy of its pullback to
   the punctured end trait) is isomorphic to `V`;
2. the canonical extension is tame at the opposite end;
3. it is special: the kernel of the special quotient of `π₁(𝔾_m)` acts trivially on its stalk;
4. every lisse sheaf on `𝔾_m` that is special in this sense and whose local monodromy at `e` is
   isomorphic to `V` is isomorphic to the canonical extension;
5. if the inertia group acts on `V` through a finite quotient, the geometric fundamental group of
   `𝔾_m` acts on the stalk of the canonical extension through a finite quotient;
6. functoriality: for an intertwiner `f : V → W`, `canonicalExtensionMap` is the unique morphism of
   canonical extensions whose stalk map is `f` under the stalk identifications;
7. exactness: a short exact sequence of representations gives a short exact sequence of the
   canonical extensions;
8. `V ⊗ W` is continuous, the tensor product of the canonical extensions is lisse, and the
   canonical extension of `V ⊗ W` is isomorphic to that tensor product;
9. for a lisse sheaf `L` on `Spec k`, the local monodromy of its pullback to the punctured end
   trait is continuous, and its canonical extension is isomorphic to the pullback of `L` to
   `𝔾_m`;
10. for a finite extension `k₁` of `k`, compatible base-change data `j`, `ι` and `res` exist.
    For each such choice, the restriction of `V` along `res` is continuous, and its canonical
    extension over `k₁` along any Katz–Gabber retraction `r₁` is isomorphic to the pullback of
    the canonical extension of `V` along `gmBaseChange k k₁`. -/
def CanonicalExtensionMonodromyStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] (_ : ℓ ≠ ringChar k) (e : FourierEnd)
    (r : Aut (Scheme.FiniteEtale.fiber (gmEndPoint k e)) →* Gal(endGenericClosure k/endField k))
    (hr : IsKatzGabberRetraction k e r),
    (∀ (V : FiniteRepresentation.{0, u, u + 1} (PadicAlgCl ℓ) Gal(endGenericClosure k/endField k))
        (hV : IsLadicContinuous ℓ V),
      Nonempty (FiniteRepresentation.Equiv
        (fieldMonodromyRepresentation ℓ (endField k) (endGenericClosure k)
          ((canonicalExtension k ℓ e r hr.1 V hV).upperStar ℓ (puncturedEndToGm k e))) V) ∧
      IsTameLisseAt k ℓ e.opposite (canonicalExtension k ℓ e r hr.1 V hV) ∧
      (∀ g ∈ coverKernel (gmEndPoint k e) (specialCover k e), ∀ v,
        gmMonodromy k ℓ e (canonicalExtension k ℓ e r hr.1 V hV) g v = v) ∧
      (∀ F : ProEtale.LisseSheaf ℓ (gmOpen k),
        (∀ g ∈ coverKernel (gmEndPoint k e) (specialCover k e), ∀ v, gmMonodromy k ℓ e F g v = v) →
        Nonempty (FiniteRepresentation.Equiv
          (fieldMonodromyRepresentation ℓ (endField k) (endGenericClosure k)
            (F.upperStar ℓ (puncturedEndToGm k e))) V) →
        Nonempty (F ≅ canonicalExtension k ℓ e r hr.1 V hV)) ∧
      ((Set.range fun σ : (endUnramifiedField k).fixingSubgroup =>
          V.representation (σ : Gal(endGenericClosure k/endField k))).Finite →
        (Set.range fun g : gmGeometricSubgroup k (gmEndPoint k e) =>
          gmMonodromy k ℓ e (canonicalExtension k ℓ e r hr.1 V hV)
            (g : Aut (Scheme.FiniteEtale.fiber (gmEndPoint k e)))).Finite)) ∧
    (∀ (V W : FiniteRepresentation.{0, u, u + 1} (PadicAlgCl ℓ)
        Gal(endGenericClosure k/endField k)) (hV : IsLadicContinuous ℓ V)
        (hW : IsLadicContinuous ℓ W) (f : V.representation.IntertwiningMap W.representation),
      (∀ v, canonicalExtensionStalkEquiv k ℓ e r hr.1 W hW
          (gmStalkMap k ℓ e (canonicalExtensionMap k ℓ e r hr.1 hV hW f) v) =
        f (canonicalExtensionStalkEquiv k ℓ e r hr.1 V hV v)) ∧
      ∀ φ : canonicalExtension k ℓ e r hr.1 V hV ⟶ canonicalExtension k ℓ e r hr.1 W hW,
        (∀ v, canonicalExtensionStalkEquiv k ℓ e r hr.1 W hW (gmStalkMap k ℓ e φ v) =
          f (canonicalExtensionStalkEquiv k ℓ e r hr.1 V hV v)) →
        φ = canonicalExtensionMap k ℓ e r hr.1 hV hW f) ∧
    (∀ (V₁ V₂ V₃ : FiniteRepresentation.{0, u, u + 1} (PadicAlgCl ℓ)
        Gal(endGenericClosure k/endField k)) (h₁ : IsLadicContinuous ℓ V₁)
        (h₂ : IsLadicContinuous ℓ V₂) (h₃ : IsLadicContinuous ℓ V₃)
        (f : V₁.representation.IntertwiningMap V₂.representation)
        (g : V₂.representation.IntertwiningMap V₃.representation),
      Function.Injective f → Function.Surjective g →
        LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap →
        ∃ h : (canonicalExtensionMap k ℓ e r hr.1 h₁ h₂ f).hom ≫
            (canonicalExtensionMap k ℓ e r hr.1 h₂ h₃ g).hom = 0,
          (ShortComplex.mk _ _ h).ShortExact) ∧
    (∀ (V W : FiniteRepresentation.{0, u, u + 1} (PadicAlgCl ℓ)
        Gal(endGenericClosure k/endField k)) (hV : IsLadicContinuous ℓ V)
        (hW : IsLadicContinuous ℓ W),
      let VW := FiniteRepresentation.of (V.representation.tprod W.representation)
      let FVW := (CategoryTheory.Mod.tensorLeft (canonicalExtension k ℓ e r hr.1 W hW).obj).obj
        (canonicalExtension k ℓ e r hr.1 V hV).obj
      ∃ (hVW : IsLadicContinuous ℓ VW) (hl : ProEtale.IsAdicLisseSheaf FVW),
        Nonempty (canonicalExtension k ℓ e r hr.1 VW hVW ≅ ⟨FVW, hl⟩)) ∧
    (∀ L : ProEtale.LisseSheaf ℓ (Spec (.of k)),
      let V := fieldMonodromyRepresentation ℓ (endField k) (endGenericClosure k)
        (L.upperStar ℓ (puncturedEndToBase k e))
      ∃ hV : IsLadicContinuous ℓ V,
        Nonempty (canonicalExtension k ℓ e r hr.1 V hV ≅ L.upperStar ℓ (gmStructure k))) ∧
    ∀ (k₁ : Type u) [Field k₁] [Finite k₁] [Algebra k k₁],
      (∃ j ι res, IsEndGaloisBaseChange k k₁ j ι res) ∧
      ∀ j ι res, IsEndGaloisBaseChange k k₁ j ι res →
      ∀ (r₁ : Aut (Scheme.FiniteEtale.fiber (gmEndPoint k₁ e)) →*
          Gal(endGenericClosure k₁/endField k₁)) (hr₁ : IsKatzGabberRetraction k₁ e r₁)
        (V : FiniteRepresentation.{0, u, u + 1} (PadicAlgCl ℓ) Gal(endGenericClosure k/endField k))
        (hV : IsLadicContinuous ℓ V),
        ∃ hV₁ : IsLadicContinuous ℓ (FiniteRepresentation.restrict res V),
          Nonempty ((canonicalExtension k ℓ e r hr.1 V hV).upperStar ℓ (gmBaseChange k k₁) ≅
            canonicalExtension k₁ ℓ e r₁ hr₁.1 (FiniteRepresentation.restrict res V) hV₁)

end Langlands.Henniart.Laumon
