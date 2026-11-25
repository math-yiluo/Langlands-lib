# Completeness of the irreducible characters of a finite group: proof

This module proves `Langlands.FiniteRep.FiniteCharacterCompletenessStatement`
(`CharacterCompletenessStatement`):

```lean
theorem finiteCharacterCompleteness (G : Type uG) [Group G] [Fintype G] :
    FiniteCharacterCompletenessStatement G
```

(name space `Langlands.FiniteRep.CharacterCompleteness`), for every finite group in any universe.

## Proof outline

The proof is Serre's (*Linear Representations*, §2.5, Proposition 6, Theorems 6 and 7).

1. **The class sum.** For `f : G → ℂ` and a representation `ρ` on `V`, `classSum f ρ = Σ_g f(g) ρ(g)`.
   Intertwining maps commute with it (`classSum_naturality`); for a class function it commutes with
   the action (`classSum_comm`: substitute `g ↦ h g h⁻¹`), so it is a self-intertwiner
   (`classSumIntertwining`). Its trace is `Σ_g f(g) χ_ρ(g)` (`trace_classSum`).
2. **Schur's lemma.** On an irreducible `ρ`, every self-intertwiner is a scalar `c` (Mathlib's
   `Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`); taking traces,
   `c · dim V = Σ_g f(g) χ_ρ(g)`, and `dim V ≠ 0`. So if this sum vanishes, so does the class sum
   (`classSum_eq_zero_of_isIrreducible`).
3. **All representations.** If `Σ_g f(g) χ(g) = 0` for every irreducible character, the class sum
   vanishes on every finite-dimensional representation (`classSum_eq_zero`), by induction on the
   dimension: split off an irreducible subrepresentation `T` (an atom of the lattice of
   subrepresentations, `FiniteCharacter.exists_isAtom`) and a complement `C` (Maschke); `T` is a
   representative of an irreducible class with the character of `T`
   (`character_classOfRepresentation`), `C` has smaller dimension, and the class sum on
   `T × C ≅ V` is computed through the two projections.
4. **The regular representation** `regularRep` on `G → ℂ`, `(g·φ)(x) = φ(g⁻¹x)`: the class sum sends the
   point mass at `1` to `f` (`classSum_regularRep_single`). Hence a class function with
   `Σ_g f(g) χ(g) = 0` for all irreducible `χ` is zero (`eq_zero_of_sum_mul_character_eq_zero`), and,
   applied to `g ↦ f(g⁻¹)`, a class function orthogonal to all irreducible characters for the
   pairing `|G|⁻¹ Σ χ(g⁻¹) f(g)` is zero (`eq_zero_of_pairing_eq_zero`).
5. **Expansion.** The irreducible characters are orthonormal (`VirtualCharacter.pairing_irreducible`),
   hence linearly independent over `ℂ` (`linearIndependent_character`) and finitely many in the
   finite-dimensional space `G → ℂ` (`finite_irreducibleClass`). For a class function `f`,
   `f − Σ_χ ⟨χ, f⟩ χ` is a class function orthogonal to every `χ`, hence zero
   (`eq_sum_pairing_smul`). This gives the span (`mem_span_character`), and with integral, resp.
   natural, coefficients the virtual character `Σ n_χ [χ]` (`mem_virtualCharacters`), resp. the
   class `Σ n_χ • a_χ` of `RepClass ℂ G` (`exists_character_eq`).
6. **Counting.** The class functions (`classFunctions G`) are the image of the injective map
   `φ ↦ φ ∘ ConjClasses.mk` from functions on conjugacy classes (`range_funLeft_mk`), so their
   dimension is the number of conjugacy classes (`finrank_classFunctions`). The irreducible
   characters form a basis of them (linearly independent and spanning), so their number is that
   dimension (`card_irreducibleClass`).

## Declarations, in order

Name space `Langlands.FiniteRep.CharacterCompleteness`; `G` a group (finite where needed),
`V : Type uV` a complex vector space.

- `classSum [Fintype G] (f : G → ℂ) (ρ : Representation ℂ G V) : V →ₗ[ℂ] V`
- `classSum_naturality (f) (φ : ρ.IntertwiningMap σ) :
  φ.toLinearMap ∘ₗ classSum f ρ = classSum f σ ∘ₗ φ.toLinearMap`
- `classSum_comm (f) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) (ρ) (h : G) :
  classSum f ρ ∘ₗ ρ h = ρ h ∘ₗ classSum f ρ`
- `classSumIntertwining (f) (hf) (ρ) : ρ.IntertwiningMap ρ`
- `trace_classSum [FiniteDimensional ℂ V] (f) (ρ) :
  LinearMap.trace ℂ V (classSum f ρ) = ∑ g : G, f g * ρ.character g`
- `classSum_eq_zero_of_isIrreducible [FiniteDimensional ℂ V] (f) (hf) (ρ)
  (hρ : Representation.IsIrreducible ρ) (h0 : ∑ g : G, f g * ρ.character g = 0) : classSum f ρ = 0`
- `classSum_eq_zero (f) (hf) (h0 : ∀ a : IrreducibleClass G, ∑ g : G, f g * character a.1 g = 0)
  (n : ℕ) : ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ G V), finrank ℂ V = n → classSum f ρ = 0`
- `regularRep : Representation ℂ G (G → ℂ)`
- `classSum_regularRep_single [DecidableEq G] (f) : classSum f regularRep (Pi.single 1 1) = f`
- `eq_zero_of_sum_mul_character_eq_zero (f) (hf) (h0) : f = 0`
- `pairing_apply (f h : G → ℂ) :
  pairing f h = (Fintype.card G : ℂ)⁻¹ * ∑ g : G, f g⁻¹ * h g`
- `pairing_smul (f h) (c : ℂ) : pairing f (c • h) = c * pairing f h`
- `eq_zero_of_pairing_eq_zero (f) (hf)
  (h0 : ∀ a : IrreducibleClass G, pairing (character a.1) f = 0) : f = 0`
- `linearIndependent_character : LinearIndependent ℂ (fun a : IrreducibleClass G => character a.1)`
- `finite_irreducibleClass : Finite (IrreducibleClass G)`
- `eq_sum_pairing_smul [Fintype (IrreducibleClass G)] (f) (hf) :
  f = ∑ a : IrreducibleClass G, pairing (character a.1) f • character a.1`
- `mem_span_character (f) (hf) :
  f ∈ Submodule.span ℂ (Set.range fun a : IrreducibleClass G => character a.1)`
- `mem_virtualCharacters (f) (hf)
  (hint : ∀ a : IrreducibleClass G, ∃ n : ℤ, pairing (character a.1) f = n) :
  f ∈ virtualCharacters (k := ℂ) (G := G)`
- `exists_character_eq (f) (hf)
  (hnat : ∀ a : IrreducibleClass G, ∃ n : ℕ, pairing (character a.1) f = n) :
  ∃ c : RepClass ℂ G, character c = f`
- `classFunctions (G) : Submodule ℂ (G → ℂ)`
- `range_funLeft_mk : LinearMap.range (LinearMap.funLeft ℂ ℂ (ConjClasses.mk : G → ConjClasses G)) =
  classFunctions G`
- `finrank_classFunctions [Fintype G] : finrank ℂ (classFunctions G) = Nat.card (ConjClasses G)`
- `card_irreducibleClass [Fintype G] : Nat.card (IrreducibleClass G) = Nat.card (ConjClasses G)`
- `finiteCharacterCompleteness (G) : FiniteCharacterCompletenessStatement G`

Here `pairing` is `Langlands.FiniteRep.VirtualCharacter.pairing`.

## Literature

Serre, *Linear Representations of Finite Groups*, GTM 42, Springer, 1977, §2.5 (printed
pp. 18–20): Proposition 6 (the class sum is a homothety on an irreducible representation, with
ratio `(1/n) Σ f(t)χ(t)`), Theorem 6 and its proof (orthogonal class functions vanish, through the
regular representation), Theorem 7 and its proof (dimension of the class functions);
§9.1 (printed p. 68): characters and virtual characters as the non-negative, resp. all, integral
combinations of irreducible characters. The Library's proof follows Serre's; Serre's "direct sum
decomposition" is the induction on the dimension of step 3.
