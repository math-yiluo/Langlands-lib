/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.CardinalGenerated
public import WeilConjectures.Mathlib.Algebra.Homology.Double
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# The generating family of monomorphic quasi-isomorphisms

Let `C` be a Grothendieck abelian category, `G : C` an object and `κ` a cardinal. In this file
we introduce a family `CochainComplex.generatingMonoQuasiIsos G κ` of monomorphic
quasi-isomorphisms in `CochainComplex C ℤ` which is meant to generate, via the small object
argument, all monomorphic quasi-isomorphisms.

The family consists of the inclusions of subobjects which are quasi-isomorphisms, into the
subquotients of a single fixed complex `CochainComplex.diskCopower G κ`: the coproduct over
`n : ℤ` of the "disk" complexes `CochainComplex.disk G κ n`, i.e. of the corepresentatives of
the functors `K ↦ (∐ (fun (_ : κ.ord.ToType) ↦ G) ⟶ K.X n)`. As it is indexed by types of
subobjects, this family is small.

The reason for this choice is the realization lemma
`CochainComplex.generatingMonoQuasiIsos_isoClosure`: any monomorphic quasi-isomorphism whose
target is degreewise `κ`-generated relative to `G` is isomorphic, as an arrow, to a morphism of
the family. Indeed, such a target is a quotient of `diskCopower G κ`
(`CochainComplex.exists_epi_diskCopower`), hence identifies with a subquotient of it.

## Main definitions and results

- `CochainComplex.diskCopower`: the ambient complex.
- `CochainComplex.generatingMonoQuasiIsos`: the family of generating monomorphic
  quasi-isomorphisms; it is small.
- `CochainComplex.generatingMonoQuasiIsos_le`: it consists of monomorphisms which are
  quasi-isomorphisms.
- `CochainComplex.generatingMonoQuasiIsos_isoClosure`: any monomorphic quasi-isomorphism
  with degreewise `κ`-generated target lies in the isomorphism closure of the family.
-/

@[expose] public section

universe w v u

namespace CochainComplex

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (G : C) (κ : Cardinal.{w})

/-- The `n`-th "disk" complex on the `κ`-fold copower of `G`: the two-term complex which
corepresents the functor `K ↦ (∐ (fun (_ : κ.ord.ToType) ↦ G) ⟶ K.X n)`. -/
noncomputable def disk (G : C) (κ : Cardinal.{w}) (n : ℤ) : CochainComplex C ℤ :=
  HomologicalComplex.evalCompCoyonedaCorepresentative (ComplexShape.up ℤ)
    (∐ (fun (_ : κ.ord.ToType) ↦ G)) n

/-- The coproduct over `n : ℤ` of the disk complexes `CochainComplex.disk G κ n`; every
degreewise `κ`-generated cochain complex is a quotient of this complex. -/
noncomputable def diskCopower (G : C) (κ : Cardinal.{w}) : CochainComplex C ℤ :=
  ∐ (fun (n : ℤ) ↦ disk G κ n)

/-- The index type of the family `CochainComplex.generatingMonoQuasiIsos G κ`: a subquotient
`cokernel K.arrow` of `CochainComplex.diskCopower G κ`, together with a subobject of it whose
inclusion is a quasi-isomorphism. -/
structure GeneratingMonoQuasiIsosIndex (G : C) (κ : Cardinal.{w}) where
  /-- a subobject of `diskCopower G κ` -/
  V : Subobject (diskCopower G κ)
  /-- a subobject of `V` -/
  K : Subobject (V : CochainComplex C ℤ)
  /-- a subobject of the quotient of `V` by `K` -/
  T : Subobject (cokernel K.arrow)
  /-- the inclusion of `T` is a quasi-isomorphism -/
  quasiIso : QuasiIso T.arrow

/-- The generating set of monomorphic quasi-isomorphisms: subobject inclusions that are
quasi-isomorphisms, into subquotients of `diskCopower G κ`. -/
def generatingMonoQuasiIsos (G : C) (κ : Cardinal.{w}) :
    MorphismProperty (CochainComplex C ℤ) :=
  MorphismProperty.ofHoms (fun (p : GeneratingMonoQuasiIsosIndex G κ) ↦ p.T.arrow)

/-- The index type `CochainComplex.GeneratingMonoQuasiIsosIndex G κ`, described as an iterated
sigma type of types of subobjects. -/
@[simps]
def generatingMonoQuasiIsosIndexEquiv :
    GeneratingMonoQuasiIsosIndex G κ ≃
      Σ (V : Subobject (diskCopower G κ)) (K : Subobject (V : CochainComplex C ℤ)),
        { T : Subobject (cokernel K.arrow) // QuasiIso T.arrow } where
  toFun p := ⟨p.V, p.K, p.T, p.quasiIso⟩
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance small_generatingMonoQuasiIsosIndex : Small.{w} (GeneratingMonoQuasiIsosIndex G κ) :=
  small_of_injective (generatingMonoQuasiIsosIndexEquiv G κ).injective

instance isSmall_generatingMonoQuasiIsos :
    MorphismProperty.IsSmall.{w} (generatingMonoQuasiIsos G κ) := by
  dsimp only [generatingMonoQuasiIsos]
  infer_instance

lemma generatingMonoQuasiIsos_le :
    generatingMonoQuasiIsos G κ ≤
      MorphismProperty.monomorphisms (CochainComplex C ℤ) ⊓
        HomologicalComplex.quasiIso C (ComplexShape.up ℤ) := by
  rintro _ _ _ ⟨p⟩
  exact ⟨inferInstanceAs (Mono _), p.quasiIso⟩

section

variable {G κ}

/-- Every degreewise `κ`-generated cochain complex is a quotient of `diskCopower G κ`. -/
lemma exists_epi_diskCopower {T : CochainComplex C ℤ}
    (hT : degreewiseCardinalGenerated G κ T) :
    ∃ (p : diskCopower G κ ⟶ T), Epi p := by
  -- in each degree `n`, the `κ`-fold copower of `G` surjects onto `T.X n`
  have H : ∀ (n : ℤ), ∃ (q : (∐ fun (_ : κ.ord.ToType) ↦ G) ⟶ T.X n), Epi q := by
    intro n
    obtain ⟨ι, hι, q, hq⟩ := hT n
    have hle : Cardinal.mk ι ≤ Cardinal.mk κ.ord.ToType := by
      rw [Cardinal.mk_ord_toType]
      exact ((hasCardinalLT_iff_cardinal_mk_lt ι κ).1 hι).le
    obtain ⟨e⟩ := (Cardinal.le_def _ _).1 hle
    obtain ⟨r, hr⟩ := exists_epi_copower_of_injective G e e.injective
    exact ⟨r ≫ q, epi_comp _ _⟩
  choose q hq using H
  -- by corepresentability, `q n` is the degree `n` part of a morphism `disk G κ n ⟶ T`
  let φ : ∀ (n : ℤ), disk G κ n ⟶ T := fun n ↦
    (HomologicalComplex.evalCompCoyonedaCorepresentable (ComplexShape.up ℤ) _ n).homEquiv.symm
      (q n)
  have hφ : ∀ (n : ℤ), Epi ((φ n).f n) := fun n ↦
    HomologicalComplex.epi_f_homEquiv_symm (q n)
  refine ⟨Sigma.desc φ, HomologicalComplex.epi_of_epi_f _ (fun n ↦ ?_)⟩
  exact epi_of_epi_fac (HomologicalComplex.congr_hom (Sigma.ι_comp_desc φ n) n)

/-- Every degreewise `κ`-generated cochain complex is a quotient of a subobject of
`diskCopower G κ`. -/
lemma exists_epi_from_subobject_diskCopower {T : CochainComplex C ℤ}
    (hT : degreewiseCardinalGenerated G κ T) :
    ∃ (V : Subobject (diskCopower G κ)) (p : (V : CochainComplex C ℤ) ⟶ T), Epi p := by
  obtain ⟨p, hp⟩ := exists_epi_diskCopower hT
  have : IsIso (⊤ : Subobject (diskCopower G κ)).arrow :=
    (Subobject.isIso_arrow_iff_eq_top ⊤).2 rfl
  exact ⟨⊤, (⊤ : Subobject (diskCopower G κ)).arrow ≫ p, epi_comp _ _⟩

/-- Any monomorphic quasi-isomorphism whose target is degreewise `κ`-generated relative to `G`
belongs to the isomorphism closure of the family `generatingMonoQuasiIsos G κ`. -/
lemma generatingMonoQuasiIsos_isoClosure {T₀ T : CochainComplex C ℤ} (i : T₀ ⟶ T)
    [Mono i] [QuasiIso i] (hT : degreewiseCardinalGenerated G κ T) :
    (generatingMonoQuasiIsos G κ).isoClosure i := by
  obtain ⟨V, p, hp⟩ := exists_epi_from_subobject_diskCopower hT
  -- `T` is the quotient of `V` by the kernel of `p`
  have hcomm : (kernelSubobject p).arrow ≫ p = 0 := kernelSubobject_arrow_comp p
  have hlim : IsLimit (KernelFork.ofι (kernelSubobject p).arrow hcomm) :=
    IsLimit.ofIsoLimit (kernelIsKernel p) (Fork.ext (kernelSubobjectIso p).symm (by simp))
  let ψ : cokernel (kernelSubobject p).arrow ≅ T :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
      (Abelian.epiIsCokernelOfKernel _ hlim)
  -- we transport `T₀` to a subobject of that quotient
  have hqi : QuasiIso (Subobject.mk (i ≫ ψ.inv)).arrow := by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk (i ≫ ψ.inv)]
    infer_instance
  have hmem : generatingMonoQuasiIsos G κ (Subobject.mk (i ≫ ψ.inv)).arrow :=
    ⟨(⟨V, kernelSubobject p, Subobject.mk (i ≫ ψ.inv), hqi⟩ : GeneratingMonoQuasiIsosIndex G κ)⟩
  have earr : Arrow.mk i ≅ Arrow.mk (Subobject.mk (i ≫ ψ.inv)).arrow :=
    Arrow.isoMk (Subobject.underlyingIso (i ≫ ψ.inv)).symm ψ.symm
      (Subobject.underlyingIso_arrow (i ≫ ψ.inv))
  exact (MorphismProperty.arrow_mk_iso_iff _ earr).2
    ((generatingMonoQuasiIsos G κ).le_isoClosure _ hmem)

end

end CochainComplex
